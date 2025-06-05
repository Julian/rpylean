# rpylean

A Lean (4) type checker written in (R)Python.

## Development

### Prerequisites

You'll need to install PyPy (2) and *also* to have a [checkout of PyPy](https://github.com/pypy/pypy) which contains the [RPython toolchain](https://rpython.readthedocs.io) in order to work on `rpylean`.

### Translation

Any RPython interpreter (program) can be run "untranslated" -- meaning as if it were a "normal" Python program on top of another Python interpreter -- or "translated", meaning as a standalone binary.
The former is great because it allows use of any Python tool to work on the interpreter, and critically, any Python *error handling* is propagated as normal.
And translated binaries are of course great because they're fast and self-contained, not depending on Python at all.
So, the former is what you often use while developing, and the latter is what we build for actual use.

To run `rpylean` untranslated (i.e. on top of a Python interpreter) run:

```sh
PYTHONPATH=<pypy-checkout>/ pypy -m rpylean check <path/to/lean4export/file>
```

or

```sh
just rpylean <any CLI args>
```

(if you follow the section below on `just`).

The argument you pass should be a file exported via [`lean4export`](https://github.com/leanprover/lean4export/).
You can find some examples in the `tests/examples` directory if you just want to see something work.

### Translating

To translate `rpylean` and build a binary run:

```sh
pypy <pypy-checkout>/rpython/bin/rpython targetrpylean.py
```

or

```sh
just translate
```

which will output a standalone `rpylean-c` binary usable with the same CLI as above.

### Testing

It's extremely important to write tests (in general) but certainly when working on RPython projects.
Translating can take around 30 seconds, so doing so each time you make a change is unrealistic.
Running the entire test suite however (as a normal Python program) takes less than a second.

There are some tests for `rpylean` which can be run via:

```sh
pypy <pypy-checkout>/pytest.py <rpylean-checkout>/tests
```

or

```sh
just test
```

### `justfile`

There's a `justfile` alongside this README which can be used to perform all of the commands mentioned above.
To use it, after [installing `just`](https://github.com/casey/just?tab=readme-ov-file#dotenv-settings) and cloning PyPy and `lean4export`, create a [`.env` file](https://github.com/casey/just?tab=readme-ov-file#dotenv-settings) containing:

```sh
PYPY_CHECKOUT=/path/to/pypy/checkout
LEAN4EXPORT_CHECKOUT=/path/to/lean4export/checkout
```

You can then run `just rpylean`, `just translate` and/or `just test`.

## Resources

* [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/) by [@ammkrn](https://github.com/ammkrn)
* [lean4export](https://github.com/leanprover/lean4export)
* [RPython's documentation](https://rpython.readthedocs.io/en/latest/rlib.html)
