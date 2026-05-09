# Spec: Closures (lazy substitution) for binder evaluation

## TL;DR

Replace eager substitution with a deferred, environment-based representation.
When the type checker has to reduce `(λx. body) arg`, it currently *walks* the
entire `body` and produces a fresh copy with `arg` plugged in. This proposal
keeps the body untouched and remembers the binding `x ↦ arg` in a small
environment that travels alongside the expression. Lookups happen on demand.

The speedup comes from converting one O(n)-sized walk per beta-reduction into
a single O(1) operation. For `app-lam.ndjson` this collapses the O(n²)
substitution cost the test deliberately exposes; for ordinary code it cuts
the same cost wherever it appears more modestly.

## What we do today

Lean expressions in this codebase use **de Bruijn indices**: bound variables
are little numbers that count outwards — `bvar 0` means "the innermost
enclosing binder", `bvar 1` means "the one outside that", and so on. The
expression `λx. λy. x` has its inner `x` written as `bvar 1` because there is
one binder (`y`) between the use and the binding (`x`).

When the type checker sees `(λx. body) arg`, it has to "do the substitution":
walk `body`, find every `bvar 0` and replace it with `arg`, decrement deeper
indices by one (because `λx`'s binder is gone), and produce the rewritten
expression. That's `_iter_instantiate` in `objects.py`. It's correct, but
every reduction allocates a fresh tree the size of `body`.

Repeating this once per nested binder gives the O(n²) total cost
`app-lam.ndjson` is designed to expose.

The current mitigations are local: each `W_App`/`W_Lambda`/`W_ForAll` carries
a one-entry cache (`_inst_cache_expr`/`_depth`/`_result`) so the *same*
substitution into the *same* subexpression is recomputed only once. That
helps DAG-shared inputs but doesn't help when the (expr, depth) pair is fresh
each time, which is most of `app-lam`.

## What closures change

Stop doing the substitution. Carry the work along.

We introduce a new expression node, conceptually:

```
Closure(env, body)  -- means "this is body, evaluated with these bindings"
```

`env` is a small list of `(depth → expression)` mappings. `body` is the
unchanged AST.

The reduction rule for `(λx. body) arg` becomes:

```
(λx. body) arg   →   Closure([0 ↦ arg], body)
```

That is: don't rewrite `body`. Just remember "when something inside this body
asks for `bvar 0`, hand it `arg` instead." That step is now a single
constant-time allocation rather than a tree walk.

When evaluation actually reaches a variable lookup — i.e. when we do need
*this specific* substituted value — we consult the env, and only then
allocate the result. If we never look at a particular subterm, we never pay
to substitute into it.

## Concrete plan

### 1. New node

Add `W_Closure(env, expr)` to `objects.py`. `env` is a list of substitutions
indexed by depth; `expr` is the wrapped expression. `W_Closure` is a normal
`W_Expr` — it can flow through the same machinery as anything else.

Provide a constructor that "smart-builds": pushing a binding onto an existing
`W_Closure` collapses the two envs rather than nesting `W_Closure`s.

### 2. WHNF teaches the new rule

In `W_App._whnf_core`, when the function position is a `W_Lambda`, return
`W_Closure([0 ↦ arg], lambda.body)` instead of calling
`lambda.body.instantiate(arg)`. That single change is where the asymptotic
win lives.

In `W_Closure._whnf_core`:

- If `expr` is a `W_BVar` and `env` provides its depth, return the bound
  value (and continue reducing).
- If `expr` is itself a `W_Closure`, merge the envs.
- Otherwise this is "closure of something not yet head-reduced" — push the
  closure inwards (e.g. `Closure(env, App(f, a))` becomes
  `App(Closure(env, f), Closure(env, a))`). This is where laziness pays
  off: we only descend when reduction asks us to.

### 3. The other code paths must read closures correctly

`def_eq`, `infer`, `incr_free_bvars`, pretty-printing, `loose_bvar_range`
— all the operations that walk expressions need a "force one layer" step
that respects closures. The pattern is the same in each: when you encounter
a `W_Closure`, peel it (apply the env to one layer of `expr`) and continue.

Most call sites already begin with a `whnf` call, so they get this for
free. The places that don't (some `infer` paths, syntactic equality) need
explicit handling.

### 4. The instantiate inline cache goes away

`_inst_cache_expr`, `_inst_cache_depth`, `_inst_cache_result` are no longer
needed once substitution is lazy — they were memoizing the eager walk that
no longer happens. Drop them from `W_App`/`W_Lambda`/`W_ForAll`. That makes
those nodes ~24 bytes smaller, which itself shaves GC cost on every run.

### 5. Correctness scaffolding

- **Index shifting under binders**: when `Closure(env, λy. b)` reduces, the
  body `b` is one level deeper than `env` was built for. **Level-indexing
  is not optional, despite what an earlier draft suggested.** The
  alternative — bumping depths in `env` when pushing under a binder, or
  wrapping bound values in `Shift(val, k)` and accumulating — reproduces
  the O(N²) pattern that `tests/perf/shift-cascade.ndjson` is designed
  to expose: each new substitution traverses the shifts left by previous
  ones. Eager substitution today is also O(N²) on shift-cascade, but with
  small constants (~4 ms at N=1000); a naïve closure implementation
  trades the small constants for closure machinery and could regress
  shift-cascade absolutely. With level-indexed envs the same workload is
  O(N) and shift-cascade gets faster, not slower. Commit to levels in
  the env from day one.
- **Forcing for output**: anything that needs a "concrete" expression — the
  pretty printer, error messages, the cache key for `_def_eq_cache` — must
  walk through closures to produce a closure-free result. A `force()`
  helper that recursively eliminates `W_Closure` layers covers this.
- **Inline cache invalidation**: every existing `_infer_cache_result`,
  `_whnf_cache_result`, and `_inst_cache_*` is keyed on node identity.
  Once `W_Closure` can wrap any node, the same logical expression has
  many wrapping shapes and these caches lose hits unless we cache on the
  underlying body and apply the env to the cached result. Plan for this
  up front; otherwise the win from skipping substitution gets eaten by
  the loss from cache misses across closure boundaries.

### 6. Tests

The existing `tests/` exercise plenty of binder-heavy code (binder tests in
`test_def_eq.py`, the tutorial cases, every inductive's recursor). They
should all pass unchanged; closures are an internal representation change.

## Why this and not the alternatives

I considered three options. Here's why closures win:

**Locally nameless** (some variables become "free" with fresh names rather
than indices) avoids one specific source of complexity — index shifting under
binders. It still walks the body to introduce/eliminate the free variable,
so it doesn't change the asymptotic cost on `app-lam`. The "~1.3×" claim in
an earlier draft of this spec was a guess and shouldn't be relied on. Note:
locally nameless *does* fix shift-cascade (substitute fvars, no shifts) —
which is the same property level-indexed closure envs give us.

**de Bruijn levels** (count from the outside in instead of inside out) is a
small change that makes index arithmetic cleaner — variables that were valid
at the outer scope keep the same number when you descend under a binder.
That's nice but still requires a per-substitution walk. It's worth doing as
a *companion* to closures (see point 5 above), but it doesn't solve the
underlying problem on its own.

**Closures** are the one option whose whole point is to *not do the walk*.
That's why they fix `app-lam`. But the win is real **only if** the env is
level-indexed (or the equivalent — fvars in the env, no shifts). Closures
without that discipline collapse back to eager-substitution complexity
on shift-cascade and lose their advantage on cache hit rates (see §5).

## What you'd actually feel

- **`app-lam.ndjson`**: today ~7.4 s (translated, JIT); with closures
  *and* level-indexed envs, expected to drop into the sub-second range.
  The 70% GC time goes away because the allocations driving it stop
  happening. The expected drop is conditional on the level-indexing
  discipline of §5; without it, closures help less and the cache-miss
  story (also §5) eats some of the win.
- **`Init.ndjson` type-check**: harder to predict — most of Init isn't as
  pathological as app-lam. Probably a single-digit-percent improvement,
  maybe more on the chunks dense in beta reductions.
- **`shift-cascade.ndjson`**: today ~4 ms at N=1000 (eager substitution
  is O(N²) but with small constants). With **level-indexed** closure
  envs this becomes O(N) and gets faster at scale; with naïve closure
  envs (per §5), it can regress.
- **`grind-ring-5.ndjson`**: this one's bottleneck is iota-reduction (a
  different defeq path), so closures shouldn't change the picture there
  much. Orthogonal fix — and a correctness fix, not a perf one: the
  test currently fails with a defeq error, the kernel needs
  projection-through-recursor reduction in `W_Proj._whnf_core` to
  resolve. That's arguably higher priority than closures since it
  blocks a real workload.

## Cost

Probably one focused multi-day session, not weeks. The change is **local in
spirit** (one new node, one new whnf rule) but **broad in code surface**
because closures need to flow through every place that reads expression
shapes. Risk lives in correctness — closures are subtle around index
shifting and around equality. Heavy testing against the existing tutorial
corpus should catch most issues.

## Punt list (out of scope)

- Generalized de Bruijn levels for the whole codebase.
- Sharing of common closure envs across calls (memoization).
- A separate compiled "value" representation (full NbE) — closures here are
  still *expressions*, just lazy ones.
