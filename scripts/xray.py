#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = [
#     "click>=8.1",
#     "rich>=13.0",
# ]
# ///
"""Diagnostic profiler ("X-ray") for `rpylean`.

Four complementary modes for discovering where time, TermStore records,
RPython GC heap allocations, and RPython JIT traces/bridges go:

  1. `native`: samples the translated `./rpylean-c` binary (via macOS `sample`)
     on one or more corpora and summarizes subsystem share, top self-time C
     functions, and direct/Machine-level call-graph callers of hot primitives.
  2. `allocs`: runs untranslated `pypy` over a declaration window `[start, end)`
     and attributes TermStore record allocations (and optionally `cons_app`
     counts) by call site, unfolded declaration + AST shape, leaf inference,
     and internal cache hit/miss rates.
  3. `gc-allocs`: attributes translated RPython GC nursery allocations by
     capturing stack traces on every entry to the nursery refill slow path
     (`pypy_g_IncrementalMiniMarkGC_collect_and_reserve`, via `perf` + `gdb` on
     Linux or batch `lldb` on macOS).
  4. `jit`: measures RPython JIT impact (`--jit off` vs `JIT on` or custom
     `--jit-opts`), compile time, loop/bridge/abort counts, and optional
     `--traces` bridge-trigger & guard anatomy via `PYPYLOG=jit-log-opt:`.

Examples:
  ./scripts/xray.py native navier-stokes-euler cslib
  ./scripts/xray.py allocs navier-stokes-euler --start 105000 --end 107500
  ./scripts/xray.py allocs cslib --start 220000 --end 225000 --count-cons-app
  ./scripts/xray.py gc-allocs cslib --sites
  ./scripts/xray.py jit cslib perf/grind-ring-5 perf/magma-list-deep-n36 --traces
"""

from __future__ import annotations

import collections
import json
import os
import platform
import re
import resource
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import click
from rich import box
from rich.console import Console
from rich.table import Table

_term = shutil.get_terminal_size((156, 25))
console = Console(
    highlight=False,
    width=max(156, _term.columns),
    height=_term.lines or 25,
)


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


def find_pypy_repo(explicit: Path | None) -> Path | None:
    candidates: list[Path] = []
    if explicit is not None:
        candidates.append(explicit)
    env_pypy = os.environ.get("PYPY_REPO")
    if env_pypy:
        candidates.append(Path(env_pypy))
    candidates.append(repo_root().parent / "pypy")
    for p in candidates:
        if (p / "rpython").is_dir():
            return p
    return None


# ---- Native sampling mode -------------------------------------------------

CALLGRAPH_TARGETS = [
    "pypy_g_TermStore_cons_app",
    "pypy_g_TermStore__cons_app_miss",
    "pypy_g_TermStore__cons_app_wide",
    "pypy_g_TermStore__import_with_levels",
    "pypy_g_TermStore__import_rec",
    "pypy_g_TermStore__import_fvars_rec",
    "pypy_g_TermStore__import_const_subst_rec",
    "pypy_g_TermStore__inst_multi_buf_d0",
    "pypy_g_TermStore__inst_multi_buf_closed",
    "pypy_g_TermStore__inst_multi_rev_d0",
    "pypy_g_TermStore__inst_multi_rev_closed",
    "pypy_g_TermStore__inst_d0",
    "pypy_g_Machine__infer_app",
    "pypy_g_Machine_try_unfold_head",
    "pypy_g_IncrementalMiniMarkGC_collect_and_reserve",
    "pypy_g_ArenaCollection_malloc",
]


def _short_sym(sym: str) -> str:
    return sym.replace("pypy_g_", "")


def _classify_sym(sym: str) -> str:
    s = _short_sym(sym)
    if any(k in s for k in ("_import", "import_term", "import_const", "leaf_for", "_const_leaf", "_new_leaf", "_subst_level")):
        return "Import"
    if any(k in s for k in ("_inst", "instantiate", "bind_fvar", "shift")):
        return "Instantiate / Subst"
    if any(k in s for k in ("cons_app", "cons_general", "_new_rec", "unapp_push", "TermStore_head", "IntMap", "IntSet", "PairMap", "U32Map")):
        return "Store / Tables"
    if any(k in s for k in ("infer", "_ensure_sort", "check_value", "_check_value", "_check_leaf")):
        return "Infer / Check"
    if any(k in s for k in ("def_eq", "_proj_lazy", "_try_lazy_delta", "_find", "_union")):
        return "DefEq"
    if any(k in s for k in ("whnf", "unfold", "proj", "iota", "beta", "ctor_body", "_peel_nested")):
        return "WHNF / Unfold / Proj"
    if any(k in s for k in (
        "portal", "handle_jitexception", "execute_nonspec", "MetaInterp", "Blackhole",
        "Jit", "Assembler", "Regalloc", "OptHeap", "Optimizer_", "eval_whnf",
        "eval_closed_scalar", "CodeCache", "compile_handle", "dispatch_loop",
    )):
        return "JIT / Eval"
    if any(k in s for k in ("parse", "prescan", "read_", "EnvironmentBuilder", "Stream", "FDFile", "read")):
        return "Parser / IO"
    if any(k in s for k in (
        "GC", "MiniMark", "malloc", "free", "gc_", "ll_arena", "memmove", "bzero", "memset",
        "BaseWalker", "trace__", "visit_all_objects", "remember_young", "collect_ref_rec",
    )):
        return "GC / Alloc / Mem"
    if "ll_dict_" in s:
        return "RPython Dict"
    return "Other"


def _parse_sample_output(txt: str) -> tuple[int, list[tuple[str, int]], dict[str, collections.Counter], dict[str, collections.Counter]]:
    self_rows: list[tuple[str, int]] = []
    idx = txt.find("Sort by top of stack")
    if idx >= 0:
        row_re = re.compile(r"^\s+(.+?)\s+\(in\s+[^)]+\)\s+(\d+)\s*$")
        for line in txt[idx:].splitlines()[1:]:
            if not line.strip():
                continue
            m = row_re.match(line)
            if m:
                self_rows.append((m.group(1).strip(), int(m.group(2))))

    total_samples = sum(c for _, c in self_rows)

    direct_callers: dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
    high_callers: dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
    cg_start = txt.find("Call graph:")
    cg_end = txt.find("Total number in stack")
    if cg_start >= 0 and cg_end >= 0:
        target_set = set(CALLGRAPH_TARGETS)
        stack: list[tuple[int, int, str]] = []
        line_re = re.compile(r"^([ +!:|]*)(\d+)\s+([^\s(]+)")
        for line in txt[cg_start:cg_end].splitlines():
            m = line_re.match(line)
            if not m:
                continue
            indent = len(m.group(1))
            cnt = int(m.group(2))
            fn = m.group(3)
            while stack and stack[-1][0] >= indent:
                stack.pop()
            if fn in target_set and stack and stack[-1][2] != fn:
                caller = stack[-1][2]
                if not caller.startswith("Thread_"):
                    direct_callers[fn][caller] += cnt
                for _, _, pfn in reversed(stack):
                    if (
                        pfn.startswith("pypy_g_Machine_")
                        or pfn.startswith("pypy_g_Environment")
                        or pfn.startswith("pypy_g_W_")
                    ):
                        high_callers[fn][pfn] += cnt
                        break
            stack.append((indent, cnt, fn))

    return total_samples, self_rows, direct_callers, high_callers


def _run_native_sample(binary: Path, corpus_name: str, corpus_path: Path, top_n: int, interval_ms: int) -> None:
    if platform.system() != "Darwin" or not shutil.which("sample"):
        raise click.ClickException("`xray.py native` currently requires macOS `/usr/bin/sample`.")

    fd, out_file = tempfile.mkstemp(prefix=f"rpylean-sample-{corpus_name}-", suffix=".txt")
    os.close(fd)
    try:
        env = dict(os.environ)
        env["RPYLEAN_STACK_GROWN"] = "1"
        proc = subprocess.Popen(
            [str(binary), "check", str(corpus_path)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            env=env,
        )
        sample_res = subprocess.run(
            ["sample", str(proc.pid), "300", str(interval_ms), "-mayDie", "-file", out_file],
            capture_output=True,
            text=True,
        )
        rc = proc.wait()
        if rc != 0:
            raise click.ClickException(f"{binary.name} failed on {corpus_name} (rc={rc})")
        txt = Path(out_file).read_text(errors="replace")
        if not txt:
            raise click.ClickException(
                f"Empty sample output for {corpus_name} (rc={sample_res.returncode}): {sample_res.stderr}"
            )
    finally:
        if os.path.exists(out_file):
            os.unlink(out_file)

    total, self_rows, direct_callers, high_callers = _parse_sample_output(txt)
    if total == 0:
        console.print(f"[yellow]{corpus_name}: 0 samples collected (corpus too fast for {interval_ms}ms interval?)[/yellow]")
        return

    # 1. Subsystem breakdown
    by_sub: collections.Counter[str] = collections.Counter()
    for sym, cnt in self_rows:
        by_sub[_classify_sym(sym)] += cnt

    sub_tbl = Table(
        title=f"Native Sample — {corpus_name} ({total:,} self samples @ {interval_ms}ms)",
        box=box.SIMPLE_HEAVY,
    )
    sub_tbl.add_column("Subsystem", style="bold")
    sub_tbl.add_column("Samples", justify="right")
    sub_tbl.add_column("Share", justify="right")
    for sub, cnt in by_sub.most_common():
        sub_tbl.add_row(sub, f"{cnt:,}", f"{100.0 * cnt / total:5.1f}%")
    console.print()
    console.print(sub_tbl)

    # 2. Top self-time functions
    fn_tbl = Table(title=f"Top {top_n} Self-Time Functions — {corpus_name}", box=box.SIMPLE_HEAVY)
    fn_tbl.add_column("Function", style="cyan")
    fn_tbl.add_column("Subsystem", style="dim")
    fn_tbl.add_column("Samples", justify="right")
    fn_tbl.add_column("Share", justify="right")
    fn_tbl.add_column("Cum%", justify="right")
    cum = 0
    for sym, cnt in self_rows[:top_n]:
        cum += cnt
        fn_tbl.add_row(
            _short_sym(sym),
            _classify_sym(sym),
            f"{cnt:,}",
            f"{100.0 * cnt / total:5.1f}%",
            f"{100.0 * cum / total:5.1f}%",
        )
    console.print(fn_tbl)

    # 3. Call-graph attribution for hot primitives
    cg_tbl = Table(title=f"Hot Primitive Caller Attribution — {corpus_name}", box=box.SIMPLE_HEAVY)
    cg_tbl.add_column("Target", style="bold magenta", no_wrap=True)
    cg_tbl.add_column("Incl", justify="right", no_wrap=True)
    cg_tbl.add_column("Top Direct Callers")
    cg_tbl.add_column("Top Machine Callers")
    for target in CALLGRAPH_TARGETS:
        dc = direct_callers.get(target)
        if not dc:
            continue
        tot = sum(dc.values())
        hc = high_callers.get(target, collections.Counter())
        dc_str = ", ".join(f"{_short_sym(k)}={v}" for k, v in dc.most_common(4))
        hc_str = ", ".join(f"{_short_sym(k)}={v}" for k, v in hc.most_common(4))
        cg_tbl.add_row(_short_sym(target), f"{tot:,}", dc_str, hc_str)
    console.print(cg_tbl)


# ---- PyPy semantic allocation X-ray mode ----------------------------------

_PYPY_ALLOCS_DRIVER = r'''
import json
import sys

sys.setrecursionlimit(50000)
pypy_repo = sys.argv[1]
rpylean_repo = sys.argv[2]
corpus_path = sys.argv[3]
start = int(sys.argv[4])
end = int(sys.argv[5])
count_cons_app = (sys.argv[6] == "1")
out_json = sys.argv[7]

sys.path.insert(0, pypy_repo)
sys.path.insert(0, rpylean_repo)

from rpython.rlib.streamio import open_file_as_stream
from rpylean import parser
from rpylean.parser import EnvironmentBuilder
from rpylean.objects import (
    W_App, W_Const, W_Constructor, W_Definition, W_Lambda, W_Let,
    W_Proj, W_Recursor, find_decl,
)
from rpylean.machine import TermStore, Machine, is_leaf, leaf_index

stream = open_file_as_stream(corpus_path)
parser.validate_export_metadata(stream)
builder = EnvironmentBuilder()
builder.consume(stream)
stream.close()
env = builder.finish()
decls = builder.declarations
actual_end = len(decls) if end <= 0 or end > len(decls) else end

cons_app_cnt = [0]
if count_cons_app:
    orig_cons_app = TermStore.cons_app
    def wrap_cons_app(self, fn, arg):
        cons_app_cnt[0] += 1
        return orig_cons_app(self, fn, arg)
    TermStore.cons_app = wrap_cons_app

total_recs_reset = [0]
orig_reset = TermStore.reset
def wrap_reset(self):
    total_recs_reset[0] += self.nrecs
    return orig_reset(self)
TermStore.reset = wrap_reset

op_stats = {}
def record_op(cat, caller, da, dr):
    k = cat + "|" + caller
    v = op_stats.get(k)
    if v is None:
        op_stats[k] = [1, da, dr]
    else:
        v[0] += 1
        v[1] += da
        v[2] += dr

def hook_store_op(method_name, cat):
    orig = getattr(TermStore, method_name, None)
    if orig is None:
        return
    def wrapped(self, *args, **kw):
        c0 = cons_app_cnt[0]
        r0 = self.nrecs
        f = sys._getframe(1)
        caller = "%s:%d" % (f.f_code.co_name, f.f_lineno)
        res = orig(self, *args, **kw)
        record_op(cat, caller, cons_app_cnt[0] - c0, self.nrecs - r0)
        return res
    setattr(TermStore, method_name, wrapped)

for mname, cat in [
    ("import_term", "import_term"),
    ("import_term_fvars", "import_fvars"),
    ("import_const_term", "import_const"),
    ("import_const_subst_buf", "import_const_subst"),
    ("instantiate_multi_buf", "inst_multi_buf"),
    ("instantiate_multi_rev", "inst_multi_rev"),
    ("instantiate", "instantiate"),
]:
    hook_store_op(mname, cat)

# Hook _infer_leaf
infer_leaf_totals = {"true": [0, 0, 0], "false": [0, 0, 0]}
infer_leaf_decls = {}
orig_il = getattr(Machine, "_infer_leaf", None)
if orig_il is not None:
    def wrap_il(self, h, check):
        c0 = cons_app_cnt[0]
        r0 = self.store.nrecs
        res = orig_il(self, h, check)
        da = cons_app_cnt[0] - c0
        dr = self.store.nrecs - r0
        tk = "true" if check else "false"
        infer_leaf_totals[tk][0] += 1
        infer_leaf_totals[tk][1] += da
        infer_leaf_totals[tk][2] += dr
        e = self.store.leaves[leaf_index(h)]
        if isinstance(e, W_Const):
            dk = tk + "|" + e.name.str()
            v = infer_leaf_decls.get(dk)
            if v is None:
                infer_leaf_decls[dk] = [1, da, dr]
            else:
                v[0] += 1; v[1] += da; v[2] += dr
        return res
    Machine._infer_leaf = wrap_il

# Hook _try_unfold_app_miss
def shape_of_def(d, declarations):
    if d is None or not isinstance(d.w_kind, W_Definition):
        return "other"
    cb = d.w_kind._ctor_body
    if cb is None:
        cb = d.w_kind.init_ctor_body(declarations)
    if cb.m >= 0:
        return "DelegateCB" if cb.delegate_const is not None else "DirectCB"
    cur = d.w_kind.value
    while isinstance(cur, W_Lambda):
        cur = cur.body
    while isinstance(cur, W_Let):
        cur = cur.body
    if isinstance(cur, W_Proj):
        return "Proj"
    if isinstance(cur, W_App):
        fn = cur
        while isinstance(fn, W_App):
            fn = fn.fn
        if isinstance(fn, W_Const):
            fd = find_decl(declarations, fn.name)
            if fd is not None:
                if isinstance(fd.w_kind, W_Recursor):
                    return "Rec"
                if isinstance(fd.w_kind, W_Definition):
                    return "Def"
                if isinstance(fd.w_kind, W_Constructor):
                    return "Ctor"
    return cur.__class__.__name__

unfold_by_caller = {}
unfold_by_decl = {}
orig_unf = getattr(Machine, "_try_unfold_app_miss", None)
if orig_unf is not None:
    def wrap_unf(self, h):
        c0 = cons_app_cnt[0]
        r0 = self.store.nrecs
        f = sys._getframe(1)
        f2 = f.f_back
        caller = "%s<-%s" % (f.f_code.co_name, f2.f_code.co_name if f2 else "?")
        res = orig_unf(self, h)
        if res != 0:
            da = cons_app_cnt[0] - c0
            dr = self.store.nrecs - r0
            hd = self.store.head(h)
            nm = "?"
            sh = "other"
            if is_leaf(hd):
                e = self.store.leaves[leaf_index(hd)]
                if isinstance(e, W_Const):
                    nm = e.name.str()
                    sh = shape_of_def(find_decl(self.tc.declarations, e.name), self.tc.declarations)
            ck = caller + "|" + sh
            v = unfold_by_caller.get(ck)
            if v is None: unfold_by_caller[ck] = [1, da, dr]
            else: v[0] += 1; v[1] += da; v[2] += dr
            dk = nm + "|" + sh + "|" + caller
            v2 = unfold_by_decl.get(dk)
            if v2 is None: unfold_by_decl[dk] = [1, da, dr]
            else: v2[0] += 1; v2[1] += da; v2[2] += dr
        return res
    Machine._try_unfold_app_miss = wrap_unf

# Cache counters
caches = {
    "inst_eq_hit": 0, "inst_eq_miss": 0,
    "iwl_lgen_hit": 0, "iwl_lgen_zero": 0, "iwl_lgen_evict": 0,
    "top_fvar_hit": 0, "top_fvar_miss": 0,
    "proj_cache_hit": 0, "proj_cache_miss": 0,
}

orig_ie = getattr(TermStore, "inst_eq_buf", None)
if orig_ie is not None:
    def wrap_ie(self, pat, s, n, target):
        ok = orig_ie(self, pat, s, n, target)
        if ok: caches["inst_eq_hit"] += 1
        else: caches["inst_eq_miss"] += 1
        return ok
    TermStore.inst_eq_buf = wrap_ie

orig_iwl = getattr(TermStore, "_import_with_levels", None)
if orig_iwl is not None:
    def wrap_iwl(self, e, params, clevels, lgen, rdepth):
        if e.has_level_param():
            g = e._cache >> 32
            if g == lgen: caches["iwl_lgen_hit"] += 1
            elif g == 0: caches["iwl_lgen_zero"] += 1
            else: caches["iwl_lgen_evict"] += 1
        return orig_iwl(self, e, params, clevels, lgen, rdepth)
    TermStore._import_with_levels = wrap_iwl

orig_tf = getattr(Machine, "_top_fvar", None)
if orig_tf is not None:
    def wrap_tf(self, idx, binder, dom):
        s0 = self._top_fvars.size
        r = orig_tf(self, idx, binder, dom)
        if self._top_fvars.size == s0: caches["top_fvar_hit"] += 1
        else: caches["top_fvar_miss"] += 1
        return r
    Machine._top_fvar = wrap_tf

orig_ipf = getattr(Machine, "_import_proj_field", None)
if orig_ipf is not None:
    def wrap_ipf(self, j, popped, fidxs, ptop, const, decl, raw_field):
        s0 = self._proj_field_cache.size
        r0 = self.store.nrecs
        r = orig_ipf(self, j, popped, fidxs, ptop, const, decl, raw_field)
        if self._proj_field_cache.size == s0 and self.store.nrecs == r0:
            caches["proj_cache_hit"] += 1
        else:
            caches["proj_cache_miss"] += 1
        return r
    Machine._import_proj_field = wrap_ipf

checked = 0
errors = []
for d in decls[start:actual_end]:
    res = env.type_check_one(d, measure=False)
    checked += 1
    if res.error is not None:
        errors.append(d.name.str())
        if len(errors) >= 5:
            break

from rpylean.machine import _SPARE
if _SPARE.machine is not None:
    total_recs_reset[0] += _SPARE.machine.store.nrecs

payload = {
    "total_decls": len(decls),
    "start": start,
    "end": actual_end,
    "checked": checked,
    "errors": errors,
    "total_recs": total_recs_reset[0],
    "total_cons_app": cons_app_cnt[0] if count_cons_app else None,
    "op_stats": op_stats,
    "infer_leaf_totals": infer_leaf_totals,
    "infer_leaf_decls": infer_leaf_decls,
    "unfold_by_caller": unfold_by_caller,
    "unfold_by_decl": unfold_by_decl,
    "caches": caches,
}
with open(out_json, "w") as f:
    json.dump(payload, f)
'''


def _render_allocs_report(corpus_name: str, data: dict, top_n: int) -> None:
    has_apps = data["total_cons_app"] is not None
    sort_idx = 1 if has_apps else 2  # cons_app if counted, else new_recs
    metric_label = "cons_app" if has_apps else "new_recs"

    header = (
        f"[bold]{corpus_name}[/bold] [{data['start']}..{data['end']}] "
        f"({data['checked']} decls of {data['total_decls']:,})  "
        f"total new_recs=[bold cyan]{data['total_recs']:,}[/bold cyan]"
    )
    if has_apps:
        header += f"  total cons_app=[bold magenta]{data['total_cons_app']:,}[/bold magenta]"
    if data["errors"]:
        header += f"  [red]ERRORS: {data['errors']}[/red]"
    console.print()
    console.print(header)

    # 1. Top op/caller sites
    op_tbl = Table(title=f"Top {top_n} Allocation Sites (sorted by {metric_label})", box=box.SIMPLE_HEAVY)
    op_tbl.add_column("Op", style="bold")
    op_tbl.add_column("Caller", style="cyan")
    op_tbl.add_column("Calls", justify="right")
    if has_apps:
        op_tbl.add_column("cons_app", justify="right")
    op_tbl.add_column("new_recs", justify="right")
    op_tbl.add_column("recs/call", justify="right")
    items = sorted(data["op_stats"].items(), key=lambda kv: -kv[1][sort_idx])[:top_n]
    for k, (calls, da, dr) in items:
        cat, caller = k.split("|", 1)
        row = [cat, caller, f"{calls:,}"]
        if has_apps:
            row.append(f"{da:,}")
        row.append(f"{dr:,}")
        row.append(f"{dr / max(calls, 1):.1f}")
        op_tbl.add_row(*row)
    console.print(op_tbl)

    # 2. Unfolds by (caller, shape)
    uc_tbl = Table(title=f"Unfolds by (Caller, AST Shape) — sorted by {metric_label}", box=box.SIMPLE_HEAVY)
    uc_tbl.add_column("Caller", style="cyan")
    uc_tbl.add_column("Shape", style="bold")
    uc_tbl.add_column("Calls", justify="right")
    if has_apps:
        uc_tbl.add_column("cons_app", justify="right")
    uc_tbl.add_column("new_recs", justify="right")
    for k, (calls, da, dr) in sorted(data["unfold_by_caller"].items(), key=lambda kv: -kv[1][sort_idx])[:15]:
        caller, sh = k.split("|", 1)
        row = [caller, sh, f"{calls:,}"]
        if has_apps:
            row.append(f"{da:,}")
        row.append(f"{dr:,}")
        uc_tbl.add_row(*row)
    console.print(uc_tbl)

    # 3. Top unfolded declarations
    ud_tbl = Table(title=f"Top {top_n} Unfolded Declarations (sorted by {metric_label})", box=box.SIMPLE_HEAVY)
    ud_tbl.add_column("Declaration", style="bold")
    ud_tbl.add_column("Shape", style="yellow")
    ud_tbl.add_column("Caller", style="dim")
    ud_tbl.add_column("Calls", justify="right")
    if has_apps:
        ud_tbl.add_column("cons_app", justify="right")
    ud_tbl.add_column("new_recs", justify="right")
    for k, (calls, da, dr) in sorted(data["unfold_by_decl"].items(), key=lambda kv: -kv[1][sort_idx])[:top_n]:
        nm, sh, caller = k.split("|", 2)
        row = [nm, sh, caller, f"{calls:,}"]
        if has_apps:
            row.append(f"{da:,}")
        row.append(f"{dr:,}")
        ud_tbl.add_row(*row)
    console.print(ud_tbl)

    # 4. _infer_leaf summary & caches
    il = data["infer_leaf_totals"]
    c = data["caches"]
    cache_tbl = Table(title="Leaf Inference & Cache Hit Rates", box=box.SIMPLE_HEAVY)
    cache_tbl.add_column("Metric", style="bold")
    cache_tbl.add_column("Details")

    def pct(hit: int, tot: int) -> str:
        return f"{100.0 * hit / tot:.1f}%" if tot > 0 else "n/a"

    t_il, f_il = il["true"], il["false"]
    cache_tbl.add_row(
        "_infer_leaf(check=True)",
        f"{t_il[0]:,} calls, {t_il[2]:,} new_recs" + (f", {t_il[1]:,} cons_app" if has_apps else ""),
    )
    cache_tbl.add_row(
        "_infer_leaf(check=False)",
        f"{f_il[0]:,} calls, {f_il[2]:,} new_recs" + (f", {f_il[1]:,} cons_app" if has_apps else ""),
    )
    ie_tot = c["inst_eq_hit"] + c["inst_eq_miss"]
    cache_tbl.add_row(
        "inst_eq_buf",
        f"{c['inst_eq_hit']:,} hit / {ie_tot:,} ({pct(c['inst_eq_hit'], ie_tot)})",
    )
    iwl_tot = c["iwl_lgen_hit"] + c["iwl_lgen_zero"] + c["iwl_lgen_evict"]
    cache_tbl.add_row(
        "_import_with_levels _cache",
        f"{c['iwl_lgen_hit']:,} hit ({pct(c['iwl_lgen_hit'], iwl_tot)}), "
        f"{c['iwl_lgen_zero']:,} cold, {c['iwl_lgen_evict']:,} evicted",
    )
    tf_tot = c["top_fvar_hit"] + c["top_fvar_miss"]
    cache_tbl.add_row(
        "_top_fvars",
        f"{c['top_fvar_hit']:,} hit / {tf_tot:,} ({pct(c['top_fvar_hit'], tf_tot)})",
    )
    pf_tot = c["proj_cache_hit"] + c["proj_cache_miss"]
    cache_tbl.add_row(
        "_proj_field_cache",
        f"{c['proj_cache_hit']:,} hit / {pf_tot:,} ({pct(c['proj_cache_hit'], pf_tot)})",
    )
    console.print(cache_tbl)


# ---- RPython GC nursery allocation profiling (`collect_and_reserve`) ------

_GC_HELPER_PREFIXES = (
    "pypy_g_IncrementalMiniMarkGC_",
    "pypy_g_ArenaCollection_",
    "pypy_g_ll_list",
    "pypy_g__ll_listresize",
    "pypy_g_ll_dict",
    "pypy_g_ll_str",
    "pypy_g_ll_malloc",
    "pypy_g_newlist",
    "pypy_g_rgc_",
    "pypy_g_malloc",
)


def _is_gc_or_container_helper(sym: str) -> bool:
    return any(sym.startswith(p) for p in _GC_HELPER_PREFIXES)


def _summarize_gc_stacks(
    corpus_name: str,
    symbol: str,
    stacks: list[list[tuple[str, str]]],
    top_n: int,
    sites: bool,
) -> None:
    """Render immediate-caller and semantic-caller tables for GC nursery hits.

    Each stack is a list of ``(symbol_name, symbol_plus_offset)`` frames
    starting at frame 0 (the probed collector entry point).
    """
    total = len(stacks)
    if total == 0:
        console.print(
            f"[yellow]{corpus_name}: 0 entries recorded for `{symbol}` "
            "(workload may not have filled the nursery, or symbol name mismatch).[/yellow]"
        )
        return

    imm_counts: collections.Counter[str] = collections.Counter()
    sem_counts: collections.Counter[str] = collections.Counter()
    for frames in stacks:
        if len(frames) >= 2:
            f1_sym, f1_site = frames[1]
            imm_counts[_short_sym(f1_site if sites else f1_sym)] += 1
        else:
            imm_counts["[unresolved]"] += 1

        sem = None
        for sym, site in frames[1:]:
            if not _is_gc_or_container_helper(sym) and not sym.startswith("["):
                sem = _short_sym(site if sites else sym)
                break
        sem_counts[sem or "[unresolved]"] += 1

    imm_tbl = Table(
        title=f"GC Nursery Slow-Path Immediate Callers — {corpus_name} ({total:,} entries to `{_short_sym(symbol)}`)",
        box=box.SIMPLE_HEAVY,
    )
    imm_tbl.add_column("Immediate Caller (frame #1)", style="cyan")
    imm_tbl.add_column("Entries", justify="right")
    imm_tbl.add_column("Share", justify="right")
    imm_tbl.add_column("Cum%", justify="right")
    cum = 0
    for caller, cnt in imm_counts.most_common(top_n):
        cum += cnt
        imm_tbl.add_row(caller, f"{cnt:,}", f"{100.0 * cnt / total:5.1f}%", f"{100.0 * cum / total:5.1f}%")
    console.print()
    console.print(imm_tbl)

    sem_tbl = Table(
        title=f"GC Nursery Semantic Callers (skipping list/dict/GC helpers) — {corpus_name}",
        box=box.SIMPLE_HEAVY,
    )
    sem_tbl.add_column("Semantic Caller", style="bold magenta")
    sem_tbl.add_column("Entries", justify="right")
    sem_tbl.add_column("Share", justify="right")
    sem_tbl.add_column("Cum%", justify="right")
    cum = 0
    for caller, cnt in sem_counts.most_common(top_n):
        cum += cnt
        sem_tbl.add_row(caller, f"{cnt:,}", f"{100.0 * cnt / total:5.1f}%", f"{100.0 * cum / total:5.1f}%")
    console.print(sem_tbl)


def _run_gc_allocs_darwin(
    binary: Path, corpus_name: str, corpus_path: Path, symbol: str,
    depth: int, top_n: int, sites: bool,
) -> None:
    if not shutil.which("lldb"):
        raise click.ClickException("`lldb` not found in PATH.")

    fd_cmd, cmd_file = tempfile.mkstemp(prefix="rpylean-lldb-", suffix=".lldb")
    os.close(fd_cmd)
    try:
        # Use LLDB's built-in Python script callback to capture compact frames
        # without noisy full stop-info banners on every nursery refill.
        script = f"""settings set target.env-vars RPYLEAN_STACK_GROWN=1
settings set target.process.stop-on-exec false
breakpoint set -n {symbol}
breakpoint command add -s python 1
  import sys
  out = []
  for i in range(min({depth}, frame.thread.GetNumFrames())):
      fr = frame.thread.GetFrameAtIndex(i)
      fn = fr.GetFunctionName() or fr.GetSymbol().GetName() or "[unresolved]"
      sym_addr = fr.GetSymbol().GetStartAddress().GetLoadAddress(frame.thread.GetProcess().GetTarget())
      pc = fr.GetPC()
      off = pc - sym_addr if sym_addr != 0xFFFFFFFFFFFFFFFF and pc >= sym_addr else 0
      out.append("%s+%#x" % (fn, off))
  sys.stdout.write("GCSTACK:" + "|".join(out) + "\\n")
  return False
DONE
run check {corpus_path}
quit
"""
        Path(cmd_file).write_text(script)
        r = subprocess.run(
            ["lldb", "--no-lldbinit", "--batch", "-s", cmd_file, str(binary)],
            capture_output=True,
            text=True,
        )
        stacks: list[list[tuple[str, str]]] = []
        for line in r.stdout.splitlines():
            if not line.startswith("GCSTACK:"):
                continue
            raw_frames = line[len("GCSTACK:"):].split("|")
            parsed: list[tuple[str, str]] = []
            for item in raw_frames:
                if "+0x" in item:
                    sym, _ = item.rsplit("+0x", 1)
                    parsed.append((sym, item))
                else:
                    parsed.append((item, item))
            if parsed:
                stacks.append(parsed)
        if not stacks:
            diag = (r.stderr or r.stdout)[-800:]
            if "attach failed" in diag:
                raise click.ClickException(
                    "macOS `lldb` could not attach/pause the process (debugserver requires "
                    "an interactive session with Developer Mode / `DevToolsSecurity -enable`).\n"
                    "Run `just xray gc-allocs ...` from a local terminal, or use "
                    "`just xray native ...` for sampled GC callers.\n\n"
                    f"lldb output:\n{diag}"
                )
            if r.returncode != 0:
                raise click.ClickException(f"lldb failed (rc={r.returncode}):\n{diag}")
    finally:
        if os.path.exists(cmd_file):
            os.unlink(cmd_file)

    _summarize_gc_stacks(corpus_name, symbol, stacks, top_n, sites)


def _run_gc_allocs_linux(
    binary: Path, corpus_name: str, corpus_path: Path, symbol: str,
    depth: int, top_n: int, sites: bool,
) -> None:
    for tool in ("gdb", "perf", "setarch"):
        if not shutil.which(tool):
            raise click.ClickException(f"`{tool}` not found in PATH (required on Linux).")
    # Resolve runtime address with ASLR disabled via GDB.
    g = subprocess.run(
        [
            "gdb", "-nx", "-q", "-batch", str(binary),
            "-ex", "set debuginfod enabled off",
            "-ex", "set disable-randomization on",
            "-ex", "starti",
            "-ex", f"python assert gdb.selected_inferior().pid; print('ENTRY=%#x' % int(gdb.parse_and_eval('&{symbol}')))",
        ],
        capture_output=True,
        text=True,
    )
    m = re.search(r"^ENTRY=(0x[0-9a-fA-F]+)$", g.stdout, re.M)
    if not m:
        raise click.ClickException(f"Could not resolve `{symbol}` in GDB:\n{(g.stderr or g.stdout)[-600:]}")
    addr = m.group(1)

    fd_p, perf_file = tempfile.mkstemp(prefix=f"rpylean-perf-gc-{corpus_name}-", suffix=".data")
    os.close(fd_p)
    try:
        env = dict(os.environ)
        env["RPYLEAN_STACK_GROWN"] = "1"
        rec = subprocess.run(
            [
                "setarch", platform.machine(), "-R",
                "perf", "record", "-o", perf_file,
                "-e", f"mem:{addr}:x", "-c", "1",
                "--call-graph", "dwarf,16384", "--",
                str(binary), "check", str(corpus_path),
            ],
            capture_output=True,
            text=True,
            env=env,
        )
        if rec.returncode != 0:
            raise click.ClickException(f"perf record failed:\n{rec.stderr[-600:]}")
        scr = subprocess.run(
            ["perf", "script", "-i", perf_file, "-F", "period,event,ip,sym,symoff"],
            capture_output=True,
            text=True,
        )
        stacks: list[list[tuple[str, str]]] = []
        for block in scr.stdout.split("\n\n"):
            lines = [ln.strip() for ln in block.splitlines() if ln.strip()]
            if len(lines) < 2:
                continue
            parsed: list[tuple[str, str]] = []
            for ln in lines[1 : 1 + depth]:
                parts = ln.split()
                site = parts[1] if len(parts) >= 2 else "[unresolved]"
                sym = site.split("+0x", 1)[0]
                parsed.append((sym, site))
            if parsed and parsed[0][0] == symbol:
                stacks.append(parsed)
    finally:
        if os.path.exists(perf_file):
            os.unlink(perf_file)

    _summarize_gc_stacks(corpus_name, symbol, stacks, top_n, sites)


# ---- JIT profiling mode ---------------------------------------------------

DEFAULT_JIT_CORPORA = (
    "init",
    "std",
    "cedar",
    "cslib",
    "navier-stokes-euler",
    "perf/grind-ring-5",
    "perf/magma-list-deep-n21",
    "perf/magma-list-deep-n36",
)

_RE_TIME = re.compile(r"^\s*([\d.]+)\s+real\s+([\d.]+)\s+user\s+([\d.]+)\s+sys", re.M)
_RE_INST = re.compile(r"^\s*(\d+)\s+instructions retired", re.M)
_RE_CYC = re.compile(r"^\s*(\d+)\s+cycles elapsed", re.M)
_RE_ICX = re.compile(r"^\s*(\d+)\s+involuntary context switches", re.M)
_RE_JIT_TRACING = re.compile(r"^Tracing:\s+\d+\s+([\d.]+)", re.M)
_RE_JIT_BACKEND = re.compile(r"^Backend:\s+\d+\s+([\d.]+)", re.M)
_RE_JIT_LOOPS = re.compile(r"^Total # of loops:\s*(\d+)", re.M)
_RE_JIT_BRIDGES = re.compile(r"^Total # of bridges:\s*(\d+)", re.M)
_RE_JIT_ABORT = re.compile(r"^abort:[^:]+:\s*(\d+)", re.M)
_RE_JIT_OPT_OPS = re.compile(r"^opt ops:\s*(\d+)", re.M)
_RE_JIT_NVIRT = re.compile(r"^nvirtuals:\s*(\d+)", re.M)
_RE_JIT_GUARDS = re.compile(r"^opt guards:\s*(\d+)", re.M)


def _grow_stack_preexec() -> None:
    try:
        soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
        target = hard if hard != resource.RLIM_INFINITY else 1024 * 1024 * 1024
        if target > soft:
            resource.setrlimit(resource.RLIMIT_STACK, (target, hard))
    except (ValueError, OSError):
        pass


def _measure_jit_run(
    binary: Path,
    corpus_path: Path,
    jit_args: tuple[str, ...],
    pypylog_prefix: str | None,
) -> tuple[float, int | None, int | None, int | None, str]:
    env = os.environ.copy()
    env["RPYLEAN_STACK_GROWN"] = "1"
    log_path: str | None = None
    preexec = _grow_stack_preexec
    if pypylog_prefix is not None:
        fd, log_path = tempfile.mkstemp(prefix="rpylean-xray-jit-", suffix=".log")
        os.close(fd)
        env["PYPYLOG"] = f"{pypylog_prefix}:{log_path}"
    try:
        cmd = [str(binary), *jit_args, "check", str(corpus_path)]
        if platform.system() == "Darwin":
            r = subprocess.run(
                ["/usr/bin/time", "-l", *cmd],
                capture_output=True,
                text=True,
                env=env,
                preexec_fn=preexec,
            )
            if r.returncode != 0:
                raise click.ClickException(f"{binary.name} failed on {corpus_path.name} (rc={r.returncode})")
            err = r.stderr
            m_t = _RE_TIME.search(err)
            real_s = float(m_t.group(1)) if m_t else 0.0
            m_i = _RE_INST.search(err)
            m_c = _RE_CYC.search(err)
            m_x = _RE_ICX.search(err)
            inst = int(m_i.group(1)) if m_i else None
            cyc = int(m_c.group(1)) if m_c else None
            icx = int(m_x.group(1)) if m_x else None
        else:
            import time
            t0 = time.perf_counter()
            r = subprocess.run(cmd, capture_output=True, text=True, env=env, preexec_fn=preexec)
            real_s = time.perf_counter() - t0
            if r.returncode != 0:
                raise click.ClickException(f"{binary.name} failed on {corpus_path.name} (rc={r.returncode})")
            inst = cyc = icx = None
        log_txt = Path(log_path).read_text(errors="replace") if log_path and os.path.exists(log_path) else ""
        return real_s, inst, cyc, icx, log_txt
    finally:
        if log_path and os.path.exists(log_path):
            os.unlink(log_path)


def _parse_jit_metrics(txt: str) -> dict[str, float | int]:
    m_tr = _RE_JIT_TRACING.search(txt)
    m_be = _RE_JIT_BACKEND.search(txt)
    m_lp = _RE_JIT_LOOPS.search(txt)
    m_br = _RE_JIT_BRIDGES.search(txt)
    m_op = _RE_JIT_OPT_OPS.search(txt)
    m_nv = _RE_JIT_NVIRT.search(txt)
    m_gd = _RE_JIT_GUARDS.search(txt)
    return {
        "tracing_s": float(m_tr.group(1)) if m_tr else 0.0,
        "backend_s": float(m_be.group(1)) if m_be else 0.0,
        "loops": int(m_lp.group(1)) if m_lp else 0,
        "bridges": int(m_br.group(1)) if m_br else 0,
        "aborts": sum(int(m.group(1)) for m in _RE_JIT_ABORT.finditer(txt)),
        "opt_ops": int(m_op.group(1)) if m_op else 0,
        "nvirtuals": int(m_nv.group(1)) if m_nv else 0,
        "opt_guards": int(m_gd.group(1)) if m_gd else 0,
    }


_RE_TRACE_OFF = re.compile(r"^\+\d+:\s*")
_RE_GUARD_HEX = re.compile(r"descr=<Guard(0x[0-9a-fA-F]+)>")
_RE_BRIDGE_HDR = re.compile(r"^#\s*bridge out of Guard (0x[0-9a-fA-F]+) with (\d+) ops")
_RE_CONST_CLASS = re.compile(r"ConstClass\(([^)]+)\)")
_RE_FIELD_NAME = re.compile(r"Field[PRN]\s+([^\s>]+)")


def _short_field(raw: str) -> str:
    parts = raw.split(".")
    if len(parts) >= 2:
        return f"{parts[-2]}.{parts[-1].replace('inst_', '')}"
    return raw


def _summarize_jit_traces(corpus_name: str, log_txt: str, top_n: int) -> None:
    """Summarize loops, bridges, and exact failing guards from `PYPYLOG=jit-log-opt:`."""
    loop_dmps: collections.Counter[str] = collections.Counter()
    bridge_dmps: collections.Counter[str] = collections.Counter()
    total_ops: collections.Counter[str] = collections.Counter()
    max_ops: dict[str, int] = {}
    bridge_triggers: collections.Counter[tuple[str, str]] = collections.Counter()
    bridge_trigger_ops: collections.Counter[tuple[str, str]] = collections.Counter()
    guard_info: dict[str, tuple[str, str]] = {}

    in_block = ""
    first_dmp = ""
    first_named = ""
    last_dmp = ""
    last_named = ""
    last_op = ""
    bridge_src_guard = ""
    block_ops = 0
    n_loops = 0
    n_bridges = 0

    for line in log_txt.splitlines():
        if "{jit-log-opt-loop" in line:
            in_block = "loop"
            first_dmp = first_named = last_dmp = last_named = last_op = ""
            bridge_src_guard = ""
            block_ops = 0
            continue
        if "{jit-log-opt-bridge" in line:
            in_block = "bridge"
            first_dmp = first_named = last_dmp = last_named = last_op = ""
            bridge_src_guard = ""
            block_ops = 0
            continue
        if "jit-log-opt-loop}" in line and in_block == "loop":
            lbl = first_named or first_dmp or "(no debug_merge_point)"
            loop_dmps[lbl] += 1
            total_ops[lbl] += block_ops
            if block_ops > max_ops.get(lbl, 0):
                max_ops[lbl] = block_ops
            n_loops += 1
            in_block = ""
            continue
        if "jit-log-opt-bridge}" in line and in_block == "bridge":
            lbl = first_named or first_dmp or "(no debug_merge_point)"
            bridge_dmps[lbl] += 1
            total_ops[lbl] += block_ops
            if block_ops > max_ops.get(lbl, 0):
                max_ops[lbl] = block_ops
            if bridge_src_guard:
                gkey = guard_info.get(bridge_src_guard, ("(unseen guard)", lbl))
                bridge_triggers[gkey] += 1
                bridge_trigger_ops[gkey] += block_ops
            n_bridges += 1
            in_block = ""
            continue
        if not in_block:
            continue

        s = line.strip()
        if not s or s.startswith("["):
            continue
        if s.startswith("#"):
            bm = _RE_BRIDGE_HDR.match(s)
            if bm:
                bridge_src_guard = bm.group(1)
            continue
        if s.startswith("debug_merge_point("):
            q1 = s.find("'")
            q2 = s.rfind("'")
            lbl = s[q1 + 1 : q2] if q1 >= 0 and q2 > q1 else s
            if not first_dmp:
                first_dmp = lbl
            last_dmp = lbl
            if lbl.startswith("def:") or lbl.startswith("rec:"):
                if not first_named:
                    first_named = lbl
                last_named = lbl
            continue

        s_op = _RE_TRACE_OFF.sub("", s)
        block_ops += 1
        gm = _RE_GUARD_HEX.search(s_op)
        if gm:
            op = s_op.split("(", 1)[0]
            detail = ""
            cm = _RE_CONST_CLASS.search(s_op)
            if cm:
                detail = f"({cm.group(1)})"
            elif op in ("guard_value", "guard_nonnull", "guard_isnull", "guard_true", "guard_false"):
                fm = _RE_FIELD_NAME.search(last_op)
                if fm:
                    detail = f"({_short_field(fm.group(1))})"
                elif "ConstPtr" in s_op:
                    detail = "(ConstPtr)"
                elif "int_eq" in last_op or "int_ne" in last_op or "int_lt" in last_op:
                    detail = f"({last_op.split('=', 1)[-1].strip().split('(', 1)[0]})"
            ctx = last_named or last_dmp or "(entry)"
            guard_info[gm.group(1)] = (f"{op}{detail}", ctx)
        else:
            last_op = s_op

    tbl = Table(
        title=f"JIT Trace Anatomy — {corpus_name} ({n_loops} loops, {n_bridges} bridges)",
        box=box.SIMPLE_HEAVY,
    )
    tbl.add_column("First Named def:/rec: (or merge point)", style="cyan", overflow="fold")
    tbl.add_column("Loops", justify="right")
    tbl.add_column("Bridges", justify="right")
    tbl.add_column("Total Ops", justify="right")
    tbl.add_column("Max Ops", justify="right")
    all_keys = set(loop_dmps) | set(bridge_dmps)
    ranked = sorted(all_keys, key=lambda k: (total_ops[k], bridge_dmps[k], loop_dmps[k]), reverse=True)
    for k in ranked[:top_n]:
        tbl.add_row(k, str(loop_dmps[k]), str(bridge_dmps[k]), f"{total_ops[k]:,}", f"{max_ops[k]:,}")
    console.print()
    console.print(tbl)

    if bridge_triggers:
        gtbl = Table(title=f"Top Bridge Triggers (Failing Guards) — {corpus_name}", box=box.SIMPLE_HEAVY)
        gtbl.add_column("Failing Guard", style="cyan", overflow="fold")
        gtbl.add_column("Context (nearest def:/rec:)", style="yellow", overflow="fold")
        gtbl.add_column("Bridges", justify="right")
        gtbl.add_column("Bridge Ops", justify="right")
        for gkey, cnt in bridge_triggers.most_common(top_n):
            gtbl.add_row(gkey[0], gkey[1], str(cnt), f"{bridge_trigger_ops[gkey]:,}")
        console.print(gtbl)


# ---- CLI ------------------------------------------------------------------

@click.group(context_settings={"help_option_names": ["-h", "--help"]})
def cli() -> None:
    """Diagnostic profiler for rpylean (native sampling, PyPy allocs, GC nursery)."""


@cli.command()
@click.argument("corpora", nargs=-1, required=True)
@click.option(
    "--binary",
    type=click.Path(exists=True, dir_okay=False, path_type=Path),
    default=None,
    help="Path to rpylean-c binary (default: ./rpylean-c).",
)
@click.option("--tests-dir", type=click.Path(exists=True, file_okay=False, path_type=Path), default=None)
@click.option("--top", default=25, show_default=True, help="Number of top self-time functions to show.")
@click.option("--interval-ms", default=1, show_default=True, help="Sampling interval in milliseconds.")
def native(
    corpora: tuple[str, ...],
    binary: Path | None,
    tests_dir: Path | None,
    top: int,
    interval_ms: int,
) -> None:
    """Profile translated rpylean-c via macOS `sample` and summarize hotspots."""
    bin_path = (binary or (repo_root() / "rpylean-c")).resolve()
    if not bin_path.is_file():
        raise click.ClickException(f"Binary not found: {bin_path} (run `just translate --batch`).")
    tdir = find_tests_dir(tests_dir)
    for spec in corpora:
        name, path = resolve_corpus(spec, tdir)
        _run_native_sample(bin_path, name, path, top, interval_ms)


@cli.command()
@click.argument("corpus")
@click.option("--start", default=0, show_default=True, help="First declaration index to check.")
@click.option("--end", default=5000, show_default=True, help="End declaration index (0 = end of file).")
@click.option(
    "--count-cons-app",
    is_flag=True,
    help="Also hook every TermStore.cons_app call (more detail, ~5x slower).",
)
@click.option("--top", default=20, show_default=True, help="Rows per table.")
@click.option("--tests-dir", type=click.Path(exists=True, file_okay=False, path_type=Path), default=None)
@click.option("--pypy-repo", type=click.Path(exists=True, file_okay=False, path_type=Path), default=None)
@click.option("--json-out", type=click.Path(dir_okay=False, path_type=Path), default=None)
def allocs(
    corpus: str,
    start: int,
    end: int,
    count_cons_app: bool,
    top: int,
    tests_dir: Path | None,
    pypy_repo: Path | None,
    json_out: Path | None,
) -> None:
    """Attribute record allocations, unfolds, and cache hits via untranslated PyPy."""
    pypy_bin = shutil.which("pypy")
    if not pypy_bin:
        raise click.ClickException("`pypy` not found in PATH.")
    pypy_dir = find_pypy_repo(pypy_repo)
    if pypy_dir is None:
        raise click.ClickException("PyPy/RPython source tree not found (pass --pypy-repo or set PYPY_REPO).")
    tdir = find_tests_dir(tests_dir)
    name, path = resolve_corpus(corpus, tdir)

    fd_drv, drv_file = tempfile.mkstemp(prefix="rpylean-xray-drv-", suffix=".py")
    os.close(fd_drv)
    fd_out, out_file = tempfile.mkstemp(prefix="rpylean-xray-out-", suffix=".json")
    os.close(fd_out)
    try:
        Path(drv_file).write_text(_PYPY_ALLOCS_DRIVER)
        r = subprocess.run(
            [
                pypy_bin, drv_file,
                str(pypy_dir), str(repo_root()), str(path),
                str(start), str(end),
                "1" if count_cons_app else "0",
                out_file,
            ],
            capture_output=True,
            text=True,
        )
        if r.returncode != 0:
            raise click.ClickException(
                f"PyPy driver failed (rc={r.returncode}):\n{r.stderr[-1000:]}"
            )
        data = json.loads(Path(out_file).read_text())
    finally:
        for p in (drv_file, out_file):
            if os.path.exists(p):
                os.unlink(p)

    if json_out is not None:
        json_out.write_text(json.dumps(data, indent=2) + "\n")
    _render_allocs_report(name, data, top)


@cli.command("gc-allocs")
@click.argument("corpora", nargs=-1, required=True)
@click.option(
    "--binary",
    type=click.Path(exists=True, dir_okay=False, path_type=Path),
    default=None,
    help="Path to rpylean-c binary (default: ./rpylean-c).",
)
@click.option(
    "--symbol",
    default="pypy_g_IncrementalMiniMarkGC_collect_and_reserve",
    show_default=True,
    help="Collector nursery slow-path symbol to break on.",
)
@click.option("--depth", default=24, show_default=True, help="Stack frames to capture per nursery refill.")
@click.option("--top", default=20, show_default=True, help="Rows per table.")
@click.option("--sites", is_flag=True, help="Keep caller+offset granularity instead of grouping by function.")
@click.option("--tests-dir", type=click.Path(exists=True, file_okay=False, path_type=Path), default=None)
def gc_allocs(
    corpora: tuple[str, ...],
    binary: Path | None,
    symbol: str,
    depth: int,
    top: int,
    sites: bool,
    tests_dir: Path | None,
) -> None:
    """Attribute translated RPython GC nursery allocations via slow-path breakpoints."""
    bin_path = (binary or (repo_root() / "rpylean-c")).resolve()
    if not bin_path.is_file():
        raise click.ClickException(f"Binary not found: {bin_path} (run `just translate --batch`).")
    tdir = find_tests_dir(tests_dir)
    sysname = platform.system()
    for spec in corpora:
        name, path = resolve_corpus(spec, tdir)
        if sysname == "Darwin":
            _run_gc_allocs_darwin(bin_path, name, path, symbol, depth, top, sites)
        elif sysname == "Linux":
            _run_gc_allocs_linux(bin_path, name, path, symbol, depth, top, sites)
        else:
            raise click.ClickException(f"Unsupported OS for gc-allocs: {sysname}")


@cli.command("jit")
@click.argument("corpora", nargs=-1)
@click.option(
    "--binary",
    type=click.Path(exists=True, dir_okay=False, path_type=Path),
    default=None,
    help="Path to rpylean-c binary (default: ./rpylean-c).",
)
@click.option(
    "--jit-opts",
    default=None,
    help="Custom `--jit OPTS` string to evaluate against `--jit off` (default: binary default).",
)
@click.option(
    "--traces",
    is_flag=True,
    help="Also inspect `PYPYLOG=jit-log-opt:` to rank bridge-spawning loops and guard ops.",
)
@click.option("--top", default=15, show_default=True, help="Rows per trace anatomy table.")
@click.option("--tests-dir", type=click.Path(exists=True, file_okay=False, path_type=Path), default=None)
def jit_cmd(
    corpora: tuple[str, ...],
    binary: Path | None,
    jit_opts: str | None,
    traces: bool,
    top: int,
    tests_dir: Path | None,
) -> None:
    """Measure RPython JIT impact (`--jit off` vs `JIT on`) and trace/bridge counts."""
    bin_path = (binary or (repo_root() / "rpylean-c")).resolve()
    if not bin_path.is_file():
        raise click.ClickException(f"Binary not found: {bin_path} (run `just translate --batch`).")
    tdir = find_tests_dir(tests_dir)
    specs = corpora if corpora else DEFAULT_JIT_CORPORA
    resolved = [resolve_corpus(spec, tdir) for spec in specs]
    on_args: tuple[str, ...] = ("--jit", jit_opts) if jit_opts else ()
    title = f"JIT Impact — {bin_path.name}" + (f" (--jit {jit_opts})" if jit_opts else " (default JIT)")

    tbl = Table(title=title, box=box.SIMPLE_HEAVY)
    tbl.add_column("Corpus", style="bold", no_wrap=True)
    tbl.add_column("off inst", justify="right", no_wrap=True)
    tbl.add_column("on inst", justify="right", no_wrap=True)
    tbl.add_column("inst Δ", justify="right", no_wrap=True)
    tbl.add_column("cyc Δ", justify="right", no_wrap=True)
    tbl.add_column("wall off→on", justify="right", no_wrap=True)
    tbl.add_column("wall Δ", justify="right", no_wrap=True)
    tbl.add_column("L/B/Ab", justify="right", no_wrap=True)
    tbl.add_column("Compile", justify="right", no_wrap=True)
    tbl.add_column("Opt Ops", justify="right", no_wrap=True)
    tbl.add_column("icx off/on", justify="right", no_wrap=True)

    trace_logs: list[tuple[str, str]] = []
    for name, path in resolved:
        r_off, i_off, c_off, x_off, _ = _measure_jit_run(bin_path, path, ("--jit", "off"), None)
        log_prefix = "jit-summary,jit-log-opt" if traces else "jit-summary"
        r_on, i_on, c_on, x_on, log_txt = _measure_jit_run(bin_path, path, on_args, log_prefix)
        jm = _parse_jit_metrics(log_txt)
        if traces and (jm["loops"] or jm["bridges"]):
            trace_logs.append((name, log_txt))

        def _fmt_d(old: float | None, new: float | None, deadband: float = 0.5) -> str:
            if not old or new is None:
                return "n/a"
            d = 100.0 * (new - old) / old
            txt = f"{d:+6.2f}%"
            if d <= -deadband:
                return f"[green]{txt}[/green]"
            if d >= deadband:
                return f"[red]{txt}[/red]"
            return f"[dim]{txt}[/dim]"

        compile_ms = int(round((float(jm["tracing_s"]) + float(jm["backend_s"])) * 1000))
        tbl.add_row(
            name,
            f"{i_off / 1e9:6.2f}G" if i_off is not None else "n/a",
            f"{i_on / 1e9:6.2f}G" if i_on is not None else "n/a",
            _fmt_d(i_off, i_on, 0.25),
            _fmt_d(c_off, c_on, 0.5),
            f"{r_off:5.2f}→{r_on:5.2f}s",
            _fmt_d(r_off, r_on, 1.0),
            f"{jm['loops']}/{jm['bridges']}/{jm['aborts']}",
            f"{compile_ms}ms",
            f"{int(jm['opt_ops']):,}",
            f"{x_off}/{x_on}" if x_off is not None and x_on is not None else "n/a",
        )

    console.print()
    console.print(tbl)
    if traces:
        console.print(
            "[dim]Note: --traces enables PYPYLOG=jit-log-opt I/O on the 'on' run; "
            "omit --traces for clean JIT timing.[/dim]"
        )
    for name, log_txt in trace_logs:
        _summarize_jit_traces(name, log_txt, top)


if __name__ == "__main__":
    cli()
