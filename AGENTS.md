# AGENTS.md - Development Guide for rpylean

## Overview

rpylean is a Lean type checker written in RPython.
Like any RPython project, its codebase is written in a subset of Python (2), though the full language can be used as a metaprogramming language, and tests are written in full Python.

Key considerations for the repository are:

- **Lean semantics**: a faithful implementation of Lean's type theory and dependent types
- **RPython compatibility**: code must be translatable to C via RPython's toolchain
- **hot path optimization**: RPython's JIT driver functionality should be utilized to optimize performance-critical reduction loops

---

## Developing `rpylean`

### Workflow

Before starting any work, ensure the entire test suite passes with the command indicated below.
Also be sure no unrelated work is uncommitted which is not relevant to the task at hand.
If there is unrelated work, pause to ask whether to commit it or ignore it.
You must always add tests for any bugfix or any new feature, and you must see the test fail before implementing the code change.
After seeing the test pass you should implement the minimal reasonable code change necessary to get it to pass.
While attempting to get it to pass, feel free to run just a single test or single test file so that runs are quicker.
Be sure to run the entire suite afterwards, to ensure no other tests break.
Once the suite passes, be sure translation also passes to make sure you have written valid RPython.

If asked to commit work, do not commit unrelated functionality in the same commit.
Each commit should be a single unit of work along with its tests.

### Testing

* `just test`: run all tests (via pytest)
* `just test tests/test_cli.py`: run a single test file
* `just test tests/test_cli.py::test_usage_error_on_no_args`: run a single test
* `just test-translated`: run tests which operate on the translated `rpylean-c` binary to check its basic functionality

Add `-v` to any of the above for verbose output.

#### Guidelines

The tests you add must be minimal: construct only that which is needed to exercise the specific behavior.
Avoid relying on external files or full environment setup in all but the rarest cases, and never rely on mutable shared state, other test cases or any monkey patching.
Place tests nearby other most related tests.
Tests should have one single assertion other than guard assertions in limited cases when helpful for debugging.
Assert against entire objects rather than just single attributes or fields, and consider whether tests which are long or difficult to write encourage refactoring the API they test itself.

Don't write a test docstring unless the test name itself is insufficiently clear.
If you do write a docstring, do not say anything "should" behave some way, or start with "Test that".
Just state the behavior as fact: "Type errors include the declaration name.".

### Translation

`rpylean` can be run *untranslated* on top of a PyPy interpreter via any of:

* `just rpylean`: invokes `rpylean`'s CLI (usable with any subcommands mentioned below)
* `just pypy`: invokes PyPy with `rpylean` available on the `PYTHONPATH`
* `just i`: invokes a PyPy interactive REPL with `rpylean` imported

When untranslated, `rpylean` will execute with all of Python's conveniences in place, albeit at a performance penalty.

To translate `rpylean` into a single binary:

* `just translate`: translate without JIT (faster translation), producing a `rpylean-c-nojit` binary
* `just jit`: translate with JIT (slower translation, faster binary), producing a `rpylean-c` binary

### Style & Linting

Ensure all public API added has clear (terse, accurate and precise) docstrings.

`prek run --all-files` will run pre-commit linting, though doing so will only cover a small subset of important style rules.

#### RPython

Recall that RPython requires following its restrictions, and furthermore that it is a restricted dialect of Python **2**.
In particular:

* ensure you inherit from `object` for all classes
* use `iterkeys`, `itervalues` and `iteritems` to loop over dictionary keys
* use `r_dict` when needing a dictionary whose keys are not builtin types
* use `rbigint` when needing big integers
* use `%` formatting rather than `str.format` or f-strings

#### Imports

Organize imports in this order:

1. `from __future__ import` statements (required in all files at least for `print_function`)
2. Python standard library imports (alphabetically sorted)
3. RPython standard library imports (alphabetically sorted)
4. Local `rpylean` imports (absolute imports with `rpylean.` prefix)

```python
from __future__ import print_function

from StringIO import StringIO
from pprint import pprint as pp

from rpython.rlib.jit import JitDriver, elidable, promote
from rpython.rlib.objectmodel import compute_hash
from rpython.rlib.rbigint import rbigint

from rpylean import objects
from rpylean._rjson import loads as from_json
```

## Running `rpylean`

`rpylean`'s CLI can be run via any of:

* `just rpylean ...` (untranslated)
* `rpylean-c ...` (translated with JIT after running translation)
* `rpylean-c-nojit ...` (translated without JIT after running translation)

Useful subcommands (all placeable in the `...` placeholder) include:

* `check <path/to/export.ndjson>`: check a provided NDJSON-exported Lean environment; use the `--print` option to also show what is being checked, or `--filter` or `--filter-match` to filter the environment.
* `repl <path/to/export.ndjson>`: open an interactive `rpylean` REPL with the given Lean environment loaded (commands explained below)
* `dump <path/to/export.ndjson>`: pretty print declarations from the given file

## Exporting Lean Environments

`rpylean` operates on `lean4export`-formatted export files which are NDJSON produced by running `lean4export`.
Details on the format can be found at https://github.com/leanprover/lean4export/blob/master/format_ndjson.md and a parser implementation is at `rpylean/parser.py`.
For convenience it is wrapped in our `just` setup to be runnable via:

* `just lean4export <args>`: run the `lean4export` Lean binary with arbitrary arguments
* `just export-simple path/to/File.lean`: export a single provided Lean file

Use these commands if and when you wish to check whether Lean's true behavior matches `rpylean`s by authoring some Lean code, checking Lean's output, exporting it and then checking `rpylean`'s.

## Matching Lean Behavior

When implementing features that should match Lean's behavior (especially pretty printing), use Lean via stdin with `#check` and `#eval` commands:

```bash
echo 'set_option pp.all true
#check <your-term>
#eval <your-term-if-it-has-Repr>' | lean --stdin
```

Common options:
- `pp.all true` - show full term structure
- `pp.unicode true` - use unicode symbols
- `pp.proofs true` - show proof terms

### Lean REPL

For interactive testing:
```bash
lean
# Then type commands like:
# set_option pp.all true
# #check <term>
```

Or one-liners:
```bash
echo '#check Nat.add 1 2' | lean --stdin
```
