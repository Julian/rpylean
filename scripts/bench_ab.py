#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = [
#     "click>=8.1",
#     "rich>=13.0",
# ]
# ///
"""Sequential A/B performance and soundness verifier for translated `rpylean-c`.

Compares a baseline binary against a candidate binary (default: `./rpylean-c`)
across:
  1. Lean Kernel Arena `perf/*.ndjson` soundness/performance fixtures.
  2. `translated-tests/` (via `just test-translated`).
  3. Sequential back-to-back (and optionally interleaved multi-run) A/B runs on
     arena corpora (default: init, std, cedar, cslib, navier-stokes-euler),
     measuring instructions retired, cycles elapsed, IPC, wall/user/sys time,
     and peak memory footprint.

Typical workflow (`/*rpylean-c*` is gitignored):
  # 1. Build and save a baseline before making edits
  just translate --batch && cp rpylean-c rpylean-c-base

  # 2. Make edits, run unit tests, rebuild candidate
  just test && just translate --batch

  # 3. Verify soundness and benchmark A/B
  just bench ./rpylean-c-base

  # Code-cleanup / refactoring gate (fails if any corpus regresses >0.5% inst):
  just bench ./rpylean-c-base --max-inst-regression 0.5

  # Multi-run interleaved median on selected corpora (or arbitrary .ndjson paths):
  just bench ./rpylean-c-base -c init -c std -c mathlib --runs 3
"""

from __future__ import annotations

import glob
import hashlib
import json
import math
import os
import platform
import re
import resource
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict, dataclass
from pathlib import Path

import click
from rich import box
from rich.console import Console
from rich.table import Table

DEFAULT_CORPORA = ("init", "std", "cedar", "cslib", "navier-stokes-euler")
JIT_PERF_FIXTURES = ("grind-ring-5.ndjson", "magma-list-deep-n21.ndjson", "magma-list-deep-n36.ndjson")

RE_DARWIN_TIME = re.compile(
    r"^\s*([\d.]+)\s+real\s+([\d.]+)\s+user\s+([\d.]+)\s+sys", re.M
)
RE_DARWIN_RSS = re.compile(r"^\s*(\d+)\s+maximum resident set size", re.M)
RE_DARWIN_INST = re.compile(r"^\s*(\d+)\s+instructions retired", re.M)
RE_DARWIN_CYC = re.compile(r"^\s*(\d+)\s+cycles elapsed", re.M)
RE_DARWIN_FOOT = re.compile(r"^\s*(\d+)\s+peak memory footprint", re.M)
RE_DARWIN_ICX = re.compile(r"^\s*(\d+)\s+involuntary context switches", re.M)

RE_LINUX_PERF_INST = re.compile(r"^\s*([\d,]+)\s+instructions(?::\S*)?", re.M)
RE_LINUX_PERF_CYC = re.compile(r"^\s*([\d,]+)\s+cycles(?::\S*)?", re.M)
RE_LINUX_PERF_TIME = re.compile(r"^\s*([\d.]+)\s+seconds time elapsed", re.M)
RE_LINUX_PERF_USER = re.compile(r"^\s*([\d.]+)\s+seconds user", re.M)
RE_LINUX_PERF_SYS = re.compile(r"^\s*([\d.]+)\s+seconds sys", re.M)
RE_LINUX_RSS_KB = re.compile(r"Maximum resident set size \(kbytes\):\s*(\d+)")
RE_LINUX_ICX = re.compile(r"Involuntary context switches:\s*(\d+)")

RE_JIT_TRACING = re.compile(r"^Tracing:\s+\d+\s+([\d.]+)", re.M)
RE_JIT_BACKEND = re.compile(r"^Backend:\s+\d+\s+([\d.]+)", re.M)
RE_JIT_LOOPS = re.compile(r"^Total # of loops:\s*(\d+)", re.M)
RE_JIT_BRIDGES = re.compile(r"^Total # of bridges:\s*(\d+)", re.M)
RE_JIT_ABORT = re.compile(r"^abort:[^:]+:\s*(\d+)", re.M)
RE_JIT_OPT_OPS = re.compile(r"^opt ops:\s*(\d+)", re.M)

STATS_KEYS = (
    "summary:",
    "def_eq calls:",
    "def_eq false:",
    "def_eq eqv",
    "def_eq proof-irrel",
    "def_eq identity",
    "beta reductions:",
    "iota fires:",
    "delta unfolds:",
)

_term = shutil.get_terminal_size((184, 25))
console = Console(
    highlight=False,
    width=max(184, _term.columns),
    height=_term.lines or 25,
)


@dataclass
class RunMetrics:
    real_s: float
    user_s: float
    sys_s: float
    inst: int | None
    cyc: int | None
    foot_mib: float | None
    rss_mib: float | None
    summary_lines: list[str]
    icx: int | None = None
    jit_loops: int | None = None
    jit_bridges: int | None = None
    jit_aborts: int | None = None
    jit_compile_s: float | None = None
    jit_opt_ops: int | None = None

    @property
    def ipc(self) -> float | None:
        if self.inst is not None and self.cyc:
            return self.inst / self.cyc
        return None


@dataclass
class AggregateMetrics:
    median: RunMetrics
    runs: list[RunMetrics]

    @property
    def inst_spread_pct(self) -> float | None:
        vals = [r.inst for r in self.runs if r.inst is not None]
        if len(vals) < 2 or not self.median.inst:
            return None
        return 100.0 * (max(vals) - min(vals)) / self.median.inst

    @property
    def cyc_spread_pct(self) -> float | None:
        vals = [r.cyc for r in self.runs if r.cyc is not None]
        if len(vals) < 2 or not self.median.cyc:
            return None
        return 100.0 * (max(vals) - min(vals)) / self.median.cyc


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def find_tests_dir(explicit: Path | None) -> Path | None:
    candidates: list[Path] = []
    if explicit is not None:
        candidates.append(explicit)
    for var, suffix in (
        ("LEAN_KERNEL_ARENA_TESTS", ()),
        ("LEAN_KERNEL_ARENA", ("_build", "tests")),
    ):
        val = os.environ.get(var)
        if val:
            candidates.append(Path(val).joinpath(*suffix))
    candidates.append(repo_root().parent / "lean-kernel-arena" / "_build" / "tests")
    for path in candidates:
        if path.is_dir():
            return path
    return None


def resolve_corpus(spec: str, tests_dir: Path | None) -> tuple[str, Path]:
    direct = Path(spec)
    if direct.is_file():
        return direct.stem, direct.resolve()
    if tests_dir is None:
        raise click.ClickException(
            f"Corpus '{spec}' is not a file path and lean-kernel-arena `_build/tests` "
            "was not found. Pass --tests-dir PATH or set LEAN_KERNEL_ARENA_TESTS."
        )
    candidate = tests_dir / (spec if spec.endswith(".ndjson") else f"{spec}.ndjson")
    if not candidate.is_file():
        raise click.ClickException(f"Corpus not found: {candidate}")
    return candidate.stem, candidate


def binary_sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()[:12]


def binary_version(path: Path) -> str:
    try:
        r = subprocess.run([str(path), "--version"], capture_output=True, text=True, timeout=5)
        out = (r.stdout or r.stderr).strip().splitlines()
        if r.returncode == 0 and out:
            return out[0]
    except Exception:
        pass
    return ""


def _extract_stats(stdout: str, stderr: str) -> list[str]:
    return [
        line.strip()
        for line in (stdout + "\n" + stderr).splitlines()
        if any(k in line for k in STATS_KEYS)
    ]


def _grow_stack_preexec() -> None:
    try:
        soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
        target = hard if hard != resource.RLIM_INFINITY else 1024 * 1024 * 1024
        if target > soft:
            resource.setrlimit(resource.RLIMIT_STACK, (target, hard))
    except (ValueError, OSError):
        pass


def _parse_jit_summary(path: str) -> tuple[int | None, int | None, int | None, float | None, int | None]:
    if not os.path.exists(path):
        return None, None, None, None, None
    txt = Path(path).read_text(errors="replace")
    if not txt.strip():
        return 0, 0, 0, 0.0, 0
    m_loops = RE_JIT_LOOPS.search(txt)
    m_bridges = RE_JIT_BRIDGES.search(txt)
    m_tr = RE_JIT_TRACING.search(txt)
    m_be = RE_JIT_BACKEND.search(txt)
    m_ops = RE_JIT_OPT_OPS.search(txt)
    loops = int(m_loops.group(1)) if m_loops else 0
    bridges = int(m_bridges.group(1)) if m_bridges else 0
    aborts = sum(int(m.group(1)) for m in RE_JIT_ABORT.finditer(txt))
    compile_s = (float(m_tr.group(1)) if m_tr else 0.0) + (float(m_be.group(1)) if m_be else 0.0)
    opt_ops = int(m_ops.group(1)) if m_ops else 0
    return loops, bridges, aborts, compile_s, opt_ops


def _run_darwin(
    binary: Path,
    corpus_path: Path,
    extra: tuple[str, ...],
    pre_args: tuple[str, ...] = (),
    track_jit: bool = True,
) -> RunMetrics:
    env = os.environ.copy()
    env["RPYLEAN_STACK_GROWN"] = "1"
    jit_log: str | None = None
    preexec = _grow_stack_preexec
    if track_jit and "--jit" not in pre_args:
        fd, jit_log = tempfile.mkstemp(prefix="rpylean-jit-", suffix=".log")
        os.close(fd)
        env["PYPYLOG"] = f"jit-summary:{jit_log}"
    try:
        r = subprocess.run(
            ["/usr/bin/time", "-l", str(binary), *pre_args, "check", *extra, str(corpus_path)],
            capture_output=True,
            text=True,
            env=env,
            preexec_fn=preexec,
        )
        if r.returncode != 0:
            raise click.ClickException(
                f"{binary.name} failed on {corpus_path.name} (rc={r.returncode}):\n"
                f"{r.stderr[-600:]}"
            )
        err = r.stderr
        m_time = RE_DARWIN_TIME.search(err)
        if not m_time:
            raise click.ClickException(
                f"Could not parse `/usr/bin/time -l` output:\n{err[-400:]}"
            )
        m_rss = RE_DARWIN_RSS.search(err)
        m_inst = RE_DARWIN_INST.search(err)
        m_cyc = RE_DARWIN_CYC.search(err)
        m_foot = RE_DARWIN_FOOT.search(err)
        m_icx = RE_DARWIN_ICX.search(err)
        jl, jb, ja, jc, jo = _parse_jit_summary(jit_log) if jit_log else (None, None, None, None, None)
        return RunMetrics(
            real_s=float(m_time.group(1)),
            user_s=float(m_time.group(2)),
            sys_s=float(m_time.group(3)),
            inst=int(m_inst.group(1)) if m_inst else None,
            cyc=int(m_cyc.group(1)) if m_cyc else None,
            foot_mib=int(m_foot.group(1)) / (1024 * 1024) if m_foot else None,
            rss_mib=int(m_rss.group(1)) / (1024 * 1024) if m_rss else None,
            summary_lines=_extract_stats(r.stdout, err),
            icx=int(m_icx.group(1)) if m_icx else None,
            jit_loops=jl,
            jit_bridges=jb,
            jit_aborts=ja,
            jit_compile_s=jc,
            jit_opt_ops=jo,
        )
    finally:
        if jit_log and os.path.exists(jit_log):
            os.unlink(jit_log)


def _run_linux(
    binary: Path,
    corpus_path: Path,
    extra: tuple[str, ...],
    pre_args: tuple[str, ...] = (),
    track_jit: bool = True,
) -> RunMetrics:
    cmd = [str(binary), *pre_args, "check", *extra, str(corpus_path)]
    env = os.environ.copy()
    env["RPYLEAN_STACK_GROWN"] = "1"
    jit_log: str | None = None
    preexec = _grow_stack_preexec
    if track_jit and "--jit" not in pre_args:
        fd, jit_log = tempfile.mkstemp(prefix="rpylean-jit-", suffix=".log")
        os.close(fd)
        env["PYPYLOG"] = f"jit-summary:{jit_log}"
    try:
        if shutil.which("perf"):
            r = subprocess.run(
                ["perf", "stat", "-e", "instructions,cycles", "--", *cmd],
                capture_output=True,
                text=True,
                env=env,
                preexec_fn=preexec,
            )
            if r.returncode != 0:
                raise click.ClickException(
                    f"{binary.name} failed on {corpus_path.name} (rc={r.returncode}):\n"
                    f"{r.stderr[-600:]}"
                )
            err = r.stderr
            m_inst = RE_LINUX_PERF_INST.search(err)
            m_cyc = RE_LINUX_PERF_CYC.search(err)
            m_real = RE_LINUX_PERF_TIME.search(err)
            m_user = RE_LINUX_PERF_USER.search(err)
            m_sys = RE_LINUX_PERF_SYS.search(err)
            jl, jb, ja, jc, jo = _parse_jit_summary(jit_log) if jit_log else (None, None, None, None, None)
            return RunMetrics(
                real_s=float(m_real.group(1)) if m_real else 0.0,
                user_s=float(m_user.group(1)) if m_user else 0.0,
                sys_s=float(m_sys.group(1)) if m_sys else 0.0,
                inst=int(m_inst.group(1).replace(",", "")) if m_inst else None,
                cyc=int(m_cyc.group(1).replace(",", "")) if m_cyc else None,
                foot_mib=None,
                rss_mib=None,
                summary_lines=_extract_stats(r.stdout, err),
                jit_loops=jl,
                jit_bridges=jb,
                jit_aborts=ja,
                jit_compile_s=jc,
                jit_opt_ops=jo,
            )
        t0 = time.perf_counter()
        if Path("/usr/bin/time").exists():
            r = subprocess.run(
                ["/usr/bin/time", "-v", *cmd],
                capture_output=True,
                text=True,
                env=env,
                preexec_fn=preexec,
            )
        else:
            r = subprocess.run(cmd, capture_output=True, text=True, env=env, preexec_fn=preexec)
        real_s = time.perf_counter() - t0
        if r.returncode != 0:
            raise click.ClickException(
                f"{binary.name} failed on {corpus_path.name} (rc={r.returncode}):\n"
                f"{r.stderr[-600:]}"
            )
        m_rss = RE_LINUX_RSS_KB.search(r.stderr)
        m_icx = RE_LINUX_ICX.search(r.stderr)
        jl, jb, ja, jc, jo = _parse_jit_summary(jit_log) if jit_log else (None, None, None, None, None)
        return RunMetrics(
            real_s=real_s,
            user_s=real_s,
            sys_s=0.0,
            inst=None,
            cyc=None,
            foot_mib=None,
            rss_mib=int(m_rss.group(1)) / 1024.0 if m_rss else None,
            summary_lines=_extract_stats(r.stdout, r.stderr),
            icx=int(m_icx.group(1)) if m_icx else None,
            jit_loops=jl,
            jit_bridges=jb,
            jit_aborts=ja,
            jit_compile_s=jc,
            jit_opt_ops=jo,
        )
    finally:
        if jit_log and os.path.exists(jit_log):
            os.unlink(jit_log)


def run_one(
    label: str,
    binary: Path,
    corpus_name: str,
    corpus_path: Path,
    extra: tuple[str, ...] = (),
    pre_args: tuple[str, ...] = (),
    quiet: bool = False,
    track_jit: bool = True,
) -> RunMetrics:
    if platform.system() == "Darwin":
        m = _run_darwin(binary, corpus_path, extra, pre_args, track_jit)
    else:
        m = _run_linux(binary, corpus_path, extra, pre_args, track_jit)
    if not quiet:
        parts = [
            f"{label:14s}",
            f"{corpus_name:20s}",
            f"real={m.real_s:6.2f}s user={m.user_s:6.2f}s sys={m.sys_s:5.2f}s",
        ]
        if m.inst is not None:
            parts.append(f"inst={m.inst / 1e9:7.2f}G")
        if m.cyc is not None:
            parts.append(f"cyc={m.cyc / 1e9:6.2f}G")
        if m.ipc is not None:
            parts.append(f"ipc={m.ipc:.2f}")
        if m.foot_mib is not None:
            parts.append(f"foot={m.foot_mib:7.1f}MiB")
        if m.rss_mib is not None:
            parts.append(f"rss={m.rss_mib:6.1f}MiB")
        if m.icx is not None:
            parts.append(f"icx={m.icx}")
        if m.jit_loops is not None and (m.jit_loops > 0 or (m.jit_bridges or 0) > 0):
            ms = int(round((m.jit_compile_s or 0.0) * 1000))
            parts.append(f"jit={m.jit_loops}L/{m.jit_bridges}B({ms}ms)")
        console.print("  ".join(parts))
        for line in m.summary_lines:
            console.print(f"    [dim]{line}[/dim]")
    return m


def aggregate(runs: list[RunMetrics]) -> AggregateMetrics:
    if len(runs) == 1:
        return AggregateMetrics(median=runs[0], runs=runs)
    insts = [r.inst for r in runs if r.inst is not None]
    cycs = [r.cyc for r in runs if r.cyc is not None]
    foots = [r.foot_mib for r in runs if r.foot_mib is not None]
    rsss = [r.rss_mib for r in runs if r.rss_mib is not None]
    icxs = [r.icx for r in runs if r.icx is not None]
    jloops = [r.jit_loops for r in runs if r.jit_loops is not None]
    jbridges = [r.jit_bridges for r in runs if r.jit_bridges is not None]
    jaborts = [r.jit_aborts for r in runs if r.jit_aborts is not None]
    jcomps = [r.jit_compile_s for r in runs if r.jit_compile_s is not None]
    jops = [r.jit_opt_ops for r in runs if r.jit_opt_ops is not None]
    med = RunMetrics(
        real_s=statistics.median(r.real_s for r in runs),
        user_s=statistics.median(r.user_s for r in runs),
        sys_s=statistics.median(r.sys_s for r in runs),
        inst=int(statistics.median(insts)) if insts else None,
        cyc=int(statistics.median(cycs)) if cycs else None,
        foot_mib=statistics.median(foots) if foots else None,
        rss_mib=statistics.median(rsss) if rsss else None,
        summary_lines=runs[-1].summary_lines,
        icx=int(statistics.median(icxs)) if icxs else None,
        jit_loops=int(statistics.median(jloops)) if jloops else None,
        jit_bridges=int(statistics.median(jbridges)) if jbridges else None,
        jit_aborts=int(statistics.median(jaborts)) if jaborts else None,
        jit_compile_s=statistics.median(jcomps) if jcomps else None,
        jit_opt_ops=int(statistics.median(jops)) if jops else None,
    )
    return AggregateMetrics(median=med, runs=runs)


def run_perf_fixtures(binary: Path, tests_dir: Path | None) -> None:
    if tests_dir is None:
        console.print("[yellow]WARNING:[/yellow] arena tests dir not found; skipping perf fixtures.")
        return
    perf_files = sorted(glob.glob(str(tests_dir / "perf" / "*.ndjson")))
    if not perf_files:
        console.print(f"[yellow]WARNING:[/yellow] no perf fixtures under {tests_dir / 'perf'}")
        return
    jit_notes: list[str] = []
    for f in perf_files:
        base = os.path.basename(f)
        expect = 1 if base.startswith("refute-") else 0
        t0 = time.perf_counter()
        r = subprocess.run([str(binary), "check", f], capture_output=True)
        dt = time.perf_counter() - t0
        if r.returncode != expect:
            msg = r.stderr.decode("utf-8", "replace")[:400]
            raise click.ClickException(
                f"PERF FIXTURE FAIL {base}: rc={r.returncode} expected={expect}\n{msg}"
            )
        if base in JIT_PERF_FIXTURES:
            jit_notes.append(f"{base[:-7]}={dt:.2f}s")
    extra_note = f"  [dim]({', '.join(jit_notes)})[/dim]" if jit_notes else ""
    console.print(f"[green]Perf fixtures:[/green] {len(perf_files)}/{len(perf_files)} PASSED{extra_note}")


def run_translated_tests(candidate: Path) -> None:
    root = repo_root()
    default_bin = (root / "rpylean-c").resolve()
    if candidate.resolve() != default_bin:
        console.print(
            f"[yellow]NOTE:[/yellow] `translated-tests/` invokes {default_bin}; "
            f"ensure it matches {candidate}."
        )
    if shutil.which("just"):
        r = subprocess.run(["just", "test-translated"], cwd=str(root))
        if r.returncode != 0:
            raise SystemExit(r.returncode)
        return
    pypy_checkout = os.environ.get("PYPY_CHECKOUT")
    if not pypy_checkout:
        raise click.ClickException(
            "Cannot run translated-tests: neither `just` nor `PYPY_CHECKOUT` is set. "
            "Pass --skip-translated to skip."
        )
    env = os.environ.copy()
    env["PYTHONPATH"] = f"{pypy_checkout}:{root}"
    r = subprocess.run(
        [os.environ.get("PYPY", "pypy"), f"{pypy_checkout}/pytest.py", "translated-tests/"],
        cwd=str(root),
        env=env,
    )
    if r.returncode != 0:
        raise SystemExit(r.returncode)


def pct_delta(old: float, new: float) -> float:
    return 100.0 * (new - old) / old if old else 0.0


def geomean_delta_pct(pairs: list[tuple[float, float]]) -> float | None:
    valid = [(a, b) for a, b in pairs if a > 0 and b > 0]
    if not valid:
        return None
    log_sum = sum(math.log(b / a) for a, b in valid)
    return 100.0 * (math.exp(log_sum / len(valid)) - 1.0)


def style_delta(delta_pct: float, deadband: float = 0.25) -> str:
    text = f"{delta_pct:+6.2f}%"
    if delta_pct <= -deadband:
        return f"[green]{text}[/green]"
    if delta_pct >= deadband:
        return f"[red]{text}[/red]"
    return f"[dim]{text}[/dim]"


def style_mib_delta(delta_mib: float, deadband: float = 2.0) -> str:
    text = f"{delta_mib:+6.1f}MiB"
    if delta_mib <= -deadband:
        return f"[green]{text}[/green]"
    if delta_mib >= deadband:
        return f"[red]{text}[/red]"
    return f"[dim]{text}[/dim]"


def render_summary(
    old_label: str,
    new_label: str,
    results: dict[str, tuple[AggregateMetrics, AggregateMetrics]],
    runs: int,
    max_inst_reg: float | None,
    max_cyc_reg: float | None,
    max_foot_reg: float | None,
) -> list[str]:
    title = f"A/B Summary: {old_label} -> {new_label}"
    if runs > 1:
        title += f" (median of {runs} interleaved runs)"
    table = Table(title=title, box=box.SIMPLE_HEAVY, show_footer=True)
    table.add_column("corpus", style="bold", footer="geomean", no_wrap=True)
    table.add_column("inst (G)", justify="right", no_wrap=True)
    table.add_column("inst Δ", justify="right", no_wrap=True)
    table.add_column("cyc (G)", justify="right", no_wrap=True)
    table.add_column("cyc Δ", justify="right", no_wrap=True)
    table.add_column("wall (s)", justify="right", no_wrap=True)
    table.add_column("wall Δ", justify="right", no_wrap=True)
    table.add_column("IPC", justify="right", no_wrap=True)
    table.add_column("foot Δ", justify="right", no_wrap=True)
    has_jit = any(
        (n.median.jit_loops or 0) > 0 or (o.median.jit_loops or 0) > 0
        for o, n in results.values()
    )
    if has_jit:
        table.add_column("JIT L/B", justify="right", no_wrap=True)
    if runs > 1:
        table.add_column("cyc spread", justify="right", no_wrap=True)

    inst_pairs: list[tuple[float, float]] = []
    cyc_pairs: list[tuple[float, float]] = []
    wall_pairs: list[tuple[float, float]] = []
    regressions: list[str] = []

    for corpus, (old_agg, new_agg) in results.items():
        old = old_agg.median
        new = new_agg.median

        if old.inst is not None and new.inst is not None:
            di = pct_delta(old.inst, new.inst)
            inst_str = f"{old.inst / 1e9:7.2f} -> {new.inst / 1e9:7.2f}"
            inst_d = style_delta(di, deadband=0.15)
            inst_pairs.append((float(old.inst), float(new.inst)))
            if max_inst_reg is not None and di > max_inst_reg:
                regressions.append(
                    f"{corpus}: instructions regressed {di:+.2f}% (limit {max_inst_reg:+.2f}%)"
                )
        else:
            inst_str, inst_d = "n/a", "n/a"

        if old.cyc is not None and new.cyc is not None:
            dc = pct_delta(old.cyc, new.cyc)
            cyc_str = f"{old.cyc / 1e9:6.2f} -> {new.cyc / 1e9:6.2f}"
            cyc_d = style_delta(dc, deadband=0.5)
            cyc_pairs.append((float(old.cyc), float(new.cyc)))
            if max_cyc_reg is not None and dc > max_cyc_reg:
                regressions.append(
                    f"{corpus}: cycles regressed {dc:+.2f}% (limit {max_cyc_reg:+.2f}%)"
                )
        else:
            cyc_str, cyc_d = "n/a", "n/a"

        dw = pct_delta(old.real_s, new.real_s)
        wall_str = f"{old.real_s:6.2f} -> {new.real_s:6.2f}"
        wall_d = style_delta(dw, deadband=0.5)
        wall_pairs.append((old.real_s, new.real_s))

        if old.ipc is not None and new.ipc is not None:
            ipc_str = f"{old.ipc:4.2f}->{new.ipc:4.2f}"
        else:
            ipc_str = "n/a"

        if old.foot_mib is not None and new.foot_mib is not None:
            df = new.foot_mib - old.foot_mib
            foot_d = style_mib_delta(df)
            if max_foot_reg is not None and df > max_foot_reg:
                regressions.append(
                    f"{corpus}: peak footprint regressed {df:+.1f} MiB (limit {max_foot_reg:+.1f} MiB)"
                )
        elif old.rss_mib is not None and new.rss_mib is not None:
            df = new.rss_mib - old.rss_mib
            foot_d = style_mib_delta(df)
            if max_foot_reg is not None and df > max_foot_reg:
                regressions.append(
                    f"{corpus}: max RSS regressed {df:+.1f} MiB (limit {max_foot_reg:+.1f} MiB)"
                )
        else:
            foot_d = "n/a"

        row = [corpus, inst_str, inst_d, cyc_str, cyc_d, wall_str, wall_d, ipc_str, foot_d]
        if has_jit:
            if new.jit_loops is not None:
                ms = int(round((new.jit_compile_s or 0.0) * 1000))
                if old.jit_loops is not None and (old.jit_loops != new.jit_loops or old.jit_bridges != new.jit_bridges):
                    row.append(f"{old.jit_loops}/{old.jit_bridges}->{new.jit_loops}/{new.jit_bridges} ({ms}ms)")
                else:
                    row.append(f"{new.jit_loops}/{new.jit_bridges} ({ms}ms)")
            else:
                row.append("n/a")
        if runs > 1:
            s_old = old_agg.cyc_spread_pct
            s_new = new_agg.cyc_spread_pct
            if s_old is not None and s_new is not None:
                row.append(f"[dim]{s_old:.1f}% / {s_new:.1f}%[/dim]")
            else:
                row.append("n/a")
        table.add_row(*row)

    gi = geomean_delta_pct(inst_pairs)
    gc = geomean_delta_pct(cyc_pairs)
    gw = geomean_delta_pct(wall_pairs)
    table.columns[2].footer = style_delta(gi, deadband=0.15) if gi is not None else "n/a"
    table.columns[4].footer = style_delta(gc, deadband=0.5) if gc is not None else "n/a"
    table.columns[6].footer = style_delta(gw, deadband=0.5) if gw is not None else "n/a"
    console.print()
    console.print(table)
    return regressions


@click.command(context_settings={"help_option_names": ["-h", "--help"]})
@click.argument("baseline", type=click.Path(exists=True, dir_okay=False, path_type=Path))
@click.argument(
    "candidate",
    default=None,
    required=False,
    type=click.Path(exists=True, dir_okay=False, path_type=Path),
)
@click.option(
    "--label",
    default=None,
    help="Short label for candidate in logs (default: candidate basename).",
)
@click.option(
    "--baseline-label",
    default=None,
    help="Short label for baseline in logs (default: baseline basename).",
)
@click.option(
    "-c",
    "--corpus",
    "corpora",
    multiple=True,
    help=(
        "Arena corpus name or .ndjson path to benchmark (repeatable; "
        f"default: {', '.join(DEFAULT_CORPORA)})."
    ),
)
@click.option(
    "--tests-dir",
    type=click.Path(exists=True, file_okay=False, path_type=Path),
    default=None,
    envvar="LEAN_KERNEL_ARENA_TESTS",
    help="Path to lean-kernel-arena `_build/tests` (or set LEAN_KERNEL_ARENA_TESTS).",
)
@click.option(
    "--runs",
    type=click.IntRange(min=1),
    default=1,
    show_default=True,
    help="Number of interleaved A/B passes per corpus (reports median).",
)
@click.option(
    "--warmup",
    is_flag=True,
    help="Run one unmeasured warmup pass per corpus before timing.",
)
@click.option(
    "--skip-perf",
    is_flag=True,
    help="Skip `perf/*.ndjson` arena soundness/perf fixtures.",
)
@click.option(
    "--skip-translated",
    is_flag=True,
    help="Skip `translated-tests/` pytest suite.",
)
@click.option(
    "--only-bench",
    is_flag=True,
    help="Shorthand for `--skip-perf --skip-translated`.",
)
@click.option(
    "--jit-ab",
    is_flag=True,
    help="Also measure candidate `--jit off` vs `JIT on` on the benchmarked corpora.",
)
@click.option(
    "--stats",
    is_flag=True,
    help="Also run candidate with `--stats` on the last corpus.",
)
@click.option(
    "--max-inst-regression",
    type=float,
    default=None,
    metavar="PCT",
    help="Exit 2 if any corpus regresses instructions retired by more than PCT%.",
)
@click.option(
    "--max-cyc-regression",
    type=float,
    default=None,
    metavar="PCT",
    help="Exit 2 if any corpus regresses cycles elapsed by more than PCT%.",
)
@click.option(
    "--max-foot-regression",
    type=float,
    default=None,
    metavar="MIB",
    help="Exit 2 if any corpus regresses peak memory footprint by more than MIB MiB.",
)
@click.option(
    "--json",
    "json_out",
    type=click.Path(dir_okay=False, path_type=Path),
    default=None,
    help="Write machine-readable JSON results to this path.",
)
def main(
    baseline: Path,
    candidate: Path | None,
    label: str | None,
    baseline_label: str | None,
    corpora: tuple[str, ...],
    tests_dir: Path | None,
    runs: int,
    warmup: bool,
    skip_perf: bool,
    skip_translated: bool,
    only_bench: bool,
    jit_ab: bool,
    stats: bool,
    max_inst_regression: float | None,
    max_cyc_regression: float | None,
    max_foot_regression: float | None,
    json_out: Path | None,
) -> None:
    """Run soundness checks and sequential A/B benchmarks on rpylean-c.

    BASELINE is the reference `rpylean-c` binary. CANDIDATE defaults to
    `./rpylean-c` in the repository root.
    """
    if candidate is None:
        candidate = repo_root() / "rpylean-c"
        if not candidate.is_file():
            raise click.ClickException(
                f"Default candidate not found at {candidate}; pass CANDIDATE explicitly "
                "or run `just translate --batch`."
            )

    old_bin = baseline.resolve()
    new_bin = candidate.resolve()
    for p in (old_bin, new_bin):
        if not os.access(p, os.X_OK):
            raise click.ClickException(f"Binary is not executable: {p}")

    old_label = baseline_label or old_bin.name
    new_label = label or new_bin.name
    resolved_tests_dir = find_tests_dir(tests_dir)

    old_sha = binary_sha256(old_bin)
    new_sha = binary_sha256(new_bin)
    old_ver = binary_version(old_bin)
    new_ver = binary_version(new_bin)
    console.print(
        f"[bold]Host:[/bold] {platform.system()} {platform.machine()}  "
        f"[bold]Baseline:[/bold] {old_label} ({old_sha}{f', {old_ver}' if old_ver else ''})  "
        f"[bold]Candidate:[/bold] {new_label} ({new_sha}{f', {new_ver}' if new_ver else ''})"
    )
    if old_sha == new_sha:
        console.print(
            "[yellow]WARNING:[/yellow] baseline and candidate binaries have identical SHA-256!"
        )

    if only_bench:
        skip_perf = True
        skip_translated = True

    if not skip_perf:
        run_perf_fixtures(new_bin, resolved_tests_dir)
    if not skip_translated:
        run_translated_tests(new_bin)

    corpus_specs = corpora if corpora else DEFAULT_CORPORA
    resolved_corpora = [resolve_corpus(spec, resolved_tests_dir) for spec in corpus_specs]

    results: dict[str, tuple[AggregateMetrics, AggregateMetrics]] = {}
    for corpus_name, corpus_path in resolved_corpora:
        if warmup:
            run_one(new_label, new_bin, corpus_name, corpus_path, quiet=True)
        old_runs: list[RunMetrics] = []
        new_runs: list[RunMetrics] = []
        for i in range(runs):
            # Alternate A/B then B/A across passes to cancel thermal/load drift.
            if i % 2 == 0:
                old_runs.append(run_one(old_label, old_bin, corpus_name, corpus_path))
                new_runs.append(run_one(new_label, new_bin, corpus_name, corpus_path))
            else:
                new_runs.append(run_one(new_label, new_bin, corpus_name, corpus_path))
                old_runs.append(run_one(old_label, old_bin, corpus_name, corpus_path))
        results[corpus_name] = (aggregate(old_runs), aggregate(new_runs))

    if stats and resolved_corpora:
        last_name, last_path = resolved_corpora[-1]
        run_one(f"{new_label}-st", new_bin, last_name, last_path, extra=("--stats",))

    regressions = render_summary(
        old_label,
        new_label,
        results,
        runs,
        max_inst_regression,
        max_cyc_regression,
        max_foot_regression,
    )

    if jit_ab:
        jit_results: dict[str, tuple[AggregateMetrics, AggregateMetrics]] = {}
        console.print("\n[bold]JIT Impact Check (`--jit off` vs `JIT on` on candidate):[/bold]")
        for corpus_name, corpus_path in resolved_corpora:
            off_m = run_one(f"{new_label}:off", new_bin, corpus_name, corpus_path, pre_args=("--jit", "off"), track_jit=False)
            jit_results[corpus_name] = (aggregate([off_m]), results[corpus_name][1])
        render_summary(f"{new_label} (--jit off)", f"{new_label} (JIT on)", jit_results, 1, None, None, None)

    if json_out is not None:
        payload = {
            "host": {"system": platform.system(), "machine": platform.machine()},
            "baseline": {"path": str(old_bin), "sha256": old_sha, "version": old_ver},
            "candidate": {"path": str(new_bin), "sha256": new_sha, "version": new_ver},
            "runs": runs,
            "corpora": {
                c: {
                    "baseline": asdict(o.median),
                    "candidate": asdict(n.median),
                    "baseline_runs": [asdict(r) for r in o.runs],
                    "candidate_runs": [asdict(r) for r in n.runs],
                }
                for c, (o, n) in results.items()
            },
            "regressions": regressions,
        }
        json_out.write_text(json.dumps(payload, indent=2) + "\n")
        console.print(f"Wrote JSON report to {json_out}")

    if regressions:
        console.print("\n[bold red]REGRESSION GATE FAILED:[/bold red]")
        for msg in regressions:
            console.print(f"  [red]- {msg}[/red]")
        sys.exit(2)


if __name__ == "__main__":
    main()
