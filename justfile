set dotenv-required

pypy_checkout := env('PYPY_CHECKOUT')
rpython := pypy_checkout / "rpython/bin/rpython"

tests := justfile_directory() / "tests"
target := justfile_directory() / "targetrpylean.py"

# Run rpylean (untranslated) with any extra arguments.
rpylean *ARGS:
    PYTHONPATH="{{ pypy_checkout }}/" pypy -m rpylean {{ ARGS }}

# Translate (compile) rpylean into an rpylean-c binary.
translate *ARGS:
    pypy "{{ rpython }}" "{{ target }}" {{ ARGS }}

# Run rpylean's (untranslated) tests.
test *ARGS=tests:
    pypy "{{ pypy_checkout }}/pytest.py" {{ ARGS }}
