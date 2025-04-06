# rpylean

## Prerequisites

You'll need to install PyPy (2) and *also* to have a [checkout of PyPy](https://github.com/pypy/pypy) which contains the [RPython toolchain](https://rpython.readthedocs.io) in order to work on `rpylean`.

### `justfile`

There's a `justfile` alongside this README which can be used to perform all of the commands mentioned below.
To use it, after [installing `just`](https://github.com/casey/just?tab=readme-ov-file#dotenv-settings) and cloning PyPy, create a [`.env` file](https://github.com/casey/just?tab=readme-ov-file#dotenv-settings) containing `PYPY_CHECKOUT=/path/to/pypy/checkout`.
You can then run `just rpylean`, `just translate` and/or `just test`.

### Running Untranslated

To run `rpylean` untranslated (i.e. on top of a Python interpreter) run:

```sh
PYTHONPATH=<pypy-checkout>/ pypy -m rpylean <path/to/lean4export/file>
```

### Translating

To translate `rpylean` (and build a binary) run:

```sh
pypy <pypy-checkout>/rpython/bin/rpython targetrpylean.py
```

which will output an `rpylean-c` binary (which you can use as above with a [`lean4export`](https://github.com/ammkrn/lean4export/) file).

### Testing

There are some tests for `rpylean` which can be run via:

```sh
pypy <pypy-checkout>/pytest.py <rpylean-checkout>/tests

```

## Resources

* [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/) by [@ammkrn](https://github.com/ammkrn)
* [lean4export (format2024 version)](https://github.com/ammkrn/lean4export/tree/format2024)
