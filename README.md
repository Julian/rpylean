# rpylean

## Prerequisites

You'll need to install PyPy (2) and *also* to have a [checkout of PyPy](https://github.com/pypy/pypy) which contains the [RPython toolchain](https://rpython.readthedocs.io) in order to work on `rpylean`.

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

which will output a `targetrpylean-c` binary (which you can use as above with a [`lean4export`](https://github.com/ammkrn/lean4export/) file).

### Testing

There are some tests for `rpylean` which can be run via:

```sh
pypy <pypy-checkout>/pytest.py <rpylean-checkout>/tests

```
