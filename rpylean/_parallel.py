"""
Multi-process fork-pool batch runner for parallel declaration checking.

On POSIX systems (``os.fork`` available), the parent process parses and
registers a batch of declarations into ``Environment``, fills a work pipe
with 4-byte chunk indices using Guided Self-Scheduling (large contiguous
chunks first for ``TermStore`` cache locality and minimal COW overlap,
shrinking to small tail chunks for load balance), closes the write end,
and forks ``N - 1`` workers.  In pipelined mode, the parent immediately
continues parsing the next batch while the children check the current
batch, then joins the shared work pipe as worker 0 to drain remaining
chunks, merges all records back in exact declaration order, and drops
checked proof terms before launching the next wave.
"""

from __future__ import print_function

import errno
import os

from rpython.rlib import rgc, rposix
from rpython.rlib.objectmodel import we_are_translated
from rpython.rlib.rstring import StringBuilder

from rpylean._rlib.rcli import UsageError


HAVE_FORK = hasattr(os, "fork")

_SC_NPROCESSORS_ONLN = getattr(rposix, "sysconf_names", {}).get(
    "SC_NPROCESSORS_ONLN", -1,
)

#: Ramp-up batch sizes: start small so workers launch immediately during
#: pipelined parsing, then grow to amortize fork and COW overhead.
INITIAL_BATCH_SIZE = 8192
DEFAULT_BATCH_SIZE = 98304
#: Minimum declarations in a batch before memory-growth flushing triggers.
MIN_MEM_FLUSH_BATCH = 4096
#: Flush early if live heap grew by at least this many bytes during a batch.
MAX_BATCH_LIVE_GROWTH = 512 * 1024 * 1024
#: Initial live-heap threshold before running a non-COW major GC between waves.
GC_INITIAL_COLLECT_THRESHOLD = 1024 * 1024 * 1024
GC_MIN_HEADROOM = 512 * 1024 * 1024
GC_MAX_HEADROOM = 1536 * 1024 * 1024
#: Cap chunk count so the entire work queue (4 bytes/chunk <= 4096 B) fits
#: in a single POSIX pipe buffer write before forking.
_MAX_CHUNKS = 1024


def detect_cpus():
    """Return the number of online CPUs, or 1 if detection is unavailable."""
    if _SC_NPROCESSORS_ONLN >= 0:
        try:
            n = rposix.sysconf(_SC_NPROCESSORS_ONLN)
            if n > 0:
                return n
        except OSError:
            pass
    return 1


def parse_jobs(jobs_arg):
    """Parse ``-j`` / ``--jobs`` into a positive worker count.

    ``None`` defaults to ``1``; ``"auto"`` or ``"0"`` selects online CPU count.
    """
    if jobs_arg is None:
        return 1
    if jobs_arg == "auto" or jobs_arg == "0":
        return detect_cpus()
    try:
        n = int(jobs_arg)
    except ValueError:
        raise UsageError("Invalid --jobs: %s" % (jobs_arg,))
    if n < 0:
        raise UsageError("Invalid --jobs: %s" % (jobs_arg,))
    if n == 0:
        return detect_cpus()
    return n


def _pack_u32(v):
    return (
        chr(v & 0xFF)
        + chr((v >> 8) & 0xFF)
        + chr((v >> 16) & 0xFF)
        + chr((v >> 24) & 0xFF)
    )


def _unpack_u32(buf, pos):
    assert pos >= 0
    return (
        ord(buf[pos])
        | (ord(buf[pos + 1]) << 8)
        | (ord(buf[pos + 2]) << 16)
        | (ord(buf[pos + 3]) << 24)
    )


def _close_quiet(fd):
    if fd >= 0:
        try:
            os.close(fd)
        except OSError:
            pass


def _write_all(fd, data):
    total = len(data)
    pos = 0
    while pos < total:
        assert pos >= 0
        try:
            n = os.write(fd, data[pos:])
        except OSError as err:
            if err.errno == errno.EINTR:
                continue
            raise
        if n <= 0:
            raise OSError(errno.EPIPE, "short write")
        pos += n


def _read_u32_fd(fd):
    buf = ""
    while len(buf) < 4:
        try:
            chunk = os.read(fd, 4 - len(buf))
        except OSError as err:
            if err.errno == errno.EINTR:
                continue
            raise
        if not chunk:
            return -1
        if not buf:
            buf = chunk
        else:
            buf += chunk
    return _unpack_u32(buf, 0)


def _read_all(fd):
    sb = StringBuilder()
    while True:
        try:
            chunk = os.read(fd, 65536)
        except OSError as err:
            if err.errno == errno.EINTR:
                continue
            raise
        if not chunk:
            break
        sb.append(chunk)
    return sb.build()


def _waitpid_eintr(pid):
    while True:
        try:
            _, status = os.waitpid(pid, 0)
            return status
        except OSError as err:
            if err.errno == errno.EINTR:
                continue
            raise


class WorkerSink(object):
    """Collects per-declaration outputs/errors for one worker.

    Children serialize records into an internal ``StringBuilder`` for pipe
    transfer; parent worker 0 writes directly into batch-indexed lists.
    """

    _attrs_ = ['n_checked', '_is_child', '_buf', '_batch_len', 'errors', 'outputs']

    def __init__(self, is_child, batch_len):
        self.n_checked = 0
        self._is_child = is_child
        self._buf = StringBuilder() if is_child else None
        self._batch_len = batch_len
        self.errors = None
        self.outputs = None

    def record_checked(self):
        self.n_checked += 1

    def record_error(self, idx, text):
        if self._is_child:
            buf = self._buf
            assert buf is not None
            buf.append("E")
            buf.append(_pack_u32(idx))
            buf.append(_pack_u32(len(text)))
            buf.append(text)
        else:
            errors = self.errors
            if errors is None:
                errors = [None] * self._batch_len
                self.errors = errors
            errors[idx] = text

    def record_output(self, idx, text):
        if self._is_child:
            buf = self._buf
            assert buf is not None
            buf.append("O")
            buf.append(_pack_u32(idx))
            buf.append(_pack_u32(len(text)))
            buf.append(text)
        else:
            outputs = self.outputs
            if outputs is None:
                outputs = [None] * self._batch_len
                self.outputs = outputs
            outputs[idx] = text

    def build_payload(self):
        buf = self._buf
        assert buf is not None
        return _pack_u32(self.n_checked) + buf.build()


class BatchResult(object):
    """Merged outcome of checking a parallel batch."""

    _attrs_ = ['total_checked', 'errors', 'outputs', 'worker_errors']

    def __init__(self, total_checked, errors, outputs, worker_errors):
        self.total_checked = total_checked
        self.errors = errors
        self.outputs = outputs
        self.worker_errors = worker_errors


class ChunkRunner(object):
    """Abstract per-chunk checking callback for ``start_parallel_batch``."""

    _attrs_ = []

    def run_chunk(self, start, end, sink):
        raise NotImplementedError


class InFlightBatch(object):
    """Handle for a batch currently being checked by forked worker processes."""

    _attrs_ = [
        'n', 'chunk_starts', 'chunk_ends', 'runner',
        'work_r', 'pids', 'res_rfds',
    ]

    def __init__(self, n, chunk_starts, chunk_ends, runner, work_r, pids, res_rfds):
        self.n = n
        self.chunk_starts = chunk_starts
        self.chunk_ends = chunk_ends
        self.runner = runner
        self.work_r = work_r
        self.pids = pids
        self.res_rfds = res_rfds


def build_chunks(batch, jobs):
    """Partition ``batch`` into contiguous ``[start, end)`` chunks via Guided
    Self-Scheduling (GSS).

    Early chunks are large (``rem // (3 * jobs)``) so each worker checks long
    contiguous runs of consecutive declarations — preserving ``TermStore``
    warm-cache locality and minimizing cross-worker COW page overlap — while
    tail chunks shrink smoothly down to ``min_chunk`` for fine load balance.
    Consecutive declarations sharing a non-negative ``decl.group`` are never
    split across chunks.
    """
    n = len(batch)
    if n == 0:
        return [], []
    pipe_floor = (n + _MAX_CHUNKS - 1) // _MAX_CHUNKS
    tail_floor = n // (jobs * 32)
    if tail_floor > 32:
        tail_floor = 32
    min_chunk = pipe_floor if pipe_floor > tail_floor else tail_floor
    if min_chunk < 1:
        min_chunk = 1
    divisor = jobs * 3
    if divisor < 3:
        divisor = 3

    starts = []
    ends = []
    i = 0
    while i < n:
        rem = n - i
        c = rem // divisor
        if c < min_chunk:
            c = min_chunk
        end = i + c
        if end > n:
            end = n
        # Extend across any trailing grouped block so all members of an
        # inductive/mutual block stay in the same worker chunk.
        if end < n:
            g = batch[end - 1].group
            if g >= 0:
                while end < n and batch[end].group == g:
                    end += 1
        starts.append(i)
        ends.append(end)
        i = end
    return starts, ends


def _merge_child_payload(data, sink, batch_len):
    """Decode a child's result stream into ``sink``.

    Returns ``(child_checked, error_msg)`` where ``error_msg`` is ``None`` on
    success or a diagnostic string if the payload was truncated/corrupted.
    """
    dlen = len(data)
    if dlen < 4:
        return 0, "parallel worker returned truncated result (%d bytes)" % dlen
    child_checked = _unpack_u32(data, 0)
    pos = 4
    while pos < dlen:
        if pos + 9 > dlen:
            return child_checked, "parallel worker returned truncated record"
        tag = data[pos]
        idx = _unpack_u32(data, pos + 1)
        plen = _unpack_u32(data, pos + 5)
        pos += 9
        if plen < 0 or pos + plen > dlen or idx < 0 or idx >= batch_len:
            return child_checked, "parallel worker returned malformed record"
        assert pos >= 0
        text = data[pos:pos + plen]
        pos += plen
        if tag == "E":
            sink.record_error(idx, text)
        elif tag == "O":
            sink.record_output(idx, text)
        else:
            return child_checked, "parallel worker returned unknown record tag"
    return child_checked, None


def start_parallel_batch(batch, jobs, runner, disable_major_gc_in_child=True):
    """Fork up to ``jobs - 1`` worker children for ``batch`` and return an
    ``InFlightBatch`` handle immediately so the parent may overlap parsing the
    next batch before calling ``finish_parallel_batch``."""
    n = len(batch)
    chunk_starts, chunk_ends = build_chunks(batch, jobs)
    nchunks = len(chunk_starts)
    nworkers = jobs if jobs < nchunks else nchunks

    if not HAVE_FORK or nworkers <= 1 or n == 0:
        return InFlightBatch(n, chunk_starts, chunk_ends, runner, -1, [], [])

    return _start_fork_pool(
        n, nworkers, chunk_starts, chunk_ends, runner,
        disable_major_gc_in_child,
    )


def _start_fork_pool(
    n, nworkers, chunk_starts, chunk_ends, runner, disable_major_gc_in_child,
):
    nchunks = len(chunk_starts)
    work_r, work_w = os.pipe()
    try:
        qbuf = StringBuilder(nchunks * 4)
        for cid in range(nchunks):
            qbuf.append(_pack_u32(cid))
        _write_all(work_w, qbuf.build())
    finally:
        _close_quiet(work_w)

    pids = []
    res_rfds = []
    for _ in range(nworkers - 1):
        try:
            res_r, res_w = os.pipe()
        except OSError:
            break
        try:
            pid = os.fork()
        except OSError:
            _close_quiet(res_r)
            _close_quiet(res_w)
            break
        if pid == 0:
            # Child worker: never return into the caller.
            exit_code = 0
            try:
                _close_quiet(res_r)
                for fd in res_rfds:
                    _close_quiet(fd)
                # Keep minor nursery GC active while disabling major GC
                # steps so short-lived workers do not dirty COW pages
                # across the inherited parent heap.
                if disable_major_gc_in_child and we_are_translated():
                    rgc.disable()
                child_sink = WorkerSink(True, n)
                while True:
                    cid = _read_u32_fd(work_r)
                    if cid < 0:
                        break
                    runner.run_chunk(
                        chunk_starts[cid], chunk_ends[cid], child_sink,
                    )
                _write_all(res_w, child_sink.build_payload())
            except Exception:
                exit_code = 2
            finally:
                _close_quiet(work_r)
                _close_quiet(res_w)
                os._exit(exit_code)
        else:
            _close_quiet(res_w)
            pids.append(pid)
            res_rfds.append(res_r)

    return InFlightBatch(
        n, chunk_starts, chunk_ends, runner, work_r, pids, res_rfds,
    )


def finish_parallel_batch(inflight):
    """Join ``inflight`` as worker 0, drain remaining chunks, reap all child
    workers, and return the merged ``BatchResult``."""
    n = inflight.n
    if n == 0:
        return BatchResult(0, None, None, None)

    work_r = inflight.work_r
    chunk_starts = inflight.chunk_starts
    chunk_ends = inflight.chunk_ends
    runner = inflight.runner

    if work_r < 0:
        sink = WorkerSink(False, n)
        for i in range(len(chunk_starts)):
            runner.run_chunk(chunk_starts[i], chunk_ends[i], sink)
        return BatchResult(sink.n_checked, sink.errors, sink.outputs, None)

    return _finish_fork_pool(inflight)


def _finish_fork_pool(inflight):
    n = inflight.n
    work_r = inflight.work_r
    chunk_starts = inflight.chunk_starts
    chunk_ends = inflight.chunk_ends
    runner = inflight.runner
    pids = inflight.pids
    res_rfds = inflight.res_rfds
    inflight.work_r = -1

    parent_sink = WorkerSink(False, n)
    try:
        while True:
            cid = _read_u32_fd(work_r)
            if cid < 0:
                break
            runner.run_chunk(chunk_starts[cid], chunk_ends[cid], parent_sink)
    except Exception:
        _close_quiet(work_r)
        abort_parallel_batch(inflight)
        raise
    _close_quiet(work_r)

    total_checked = parent_sink.n_checked
    worker_errors = None
    for i in range(len(pids)):
        rfd = res_rfds[i]
        pid = pids[i]
        res_rfds[i] = -1
        pids[i] = -1
        data = ""
        read_err = None
        try:
            data = _read_all(rfd)
        except OSError as err:
            read_err = "parallel worker pipe read failed: %s" % (
                os.strerror(err.errno),
            )
        finally:
            _close_quiet(rfd)
        status = _waitpid_eintr(pid)
        if not (os.WIFEXITED(status) and os.WEXITSTATUS(status) == 0):
            if worker_errors is None:
                worker_errors = []
            if os.WIFSIGNALED(status):
                worker_errors.append(
                    "parallel worker killed by signal %d" % os.WTERMSIG(status)
                )
            elif os.WIFEXITED(status):
                worker_errors.append(
                    "parallel worker exited with code %d" % os.WEXITSTATUS(status)
                )
            else:
                worker_errors.append(
                    "parallel worker terminated abnormally (status=%d)" % status
                )
            continue
        if read_err is not None:
            if worker_errors is None:
                worker_errors = []
            worker_errors.append(read_err)
            continue
        child_checked, parse_err = _merge_child_payload(data, parent_sink, n)
        total_checked += child_checked
        if parse_err is not None:
            if worker_errors is None:
                worker_errors = []
            worker_errors.append(parse_err)

    return BatchResult(
        total_checked, parent_sink.errors, parent_sink.outputs, worker_errors,
    )


def abort_parallel_batch(inflight):
    """Best-effort cleanup of an in-flight batch on unexpected exception."""
    if inflight.work_r >= 0:
        _close_quiet(inflight.work_r)
        inflight.work_r = -1
    if not HAVE_FORK:
        return
    res_rfds = inflight.res_rfds
    pids = inflight.pids
    for i in range(len(res_rfds)):
        if res_rfds[i] >= 0:
            _close_quiet(res_rfds[i])
            res_rfds[i] = -1
    for i in range(len(pids)):
        pid = pids[i]
        if pid > 0:
            pids[i] = -1
            try:
                _waitpid_eintr(pid)
            except OSError:
                pass


def run_parallel_batch(batch, jobs, runner, disable_major_gc_in_child=True):
    """Synchronous convenience wrapper: start and immediately finish a batch."""
    return finish_parallel_batch(
        start_parallel_batch(batch, jobs, runner, disable_major_gc_in_child),
    )
