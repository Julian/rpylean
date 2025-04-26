set dotenv-required

pypy := env('PYPY', 'pypy')
pypy_checkout := env('PYPY_CHECKOUT')
rpython := pypy_checkout / "rpython/bin/rpython"

tests := justfile_directory() / "tests"
examples := tests / "examples"
target := justfile_directory() / "targetrpylean.py"

# Run rpylean (untranslated) with any extra arguments.
rpylean *ARGS:
    PYTHONPATH="{{ pypy_checkout }}/" "{{ pypy }}" -m rpylean {{ ARGS }}

# Run the rpylean REPL untranslated on an example.
example name:
    @just rpylean repl $(find "{{ examples }}" -iname "{{ name }}")/export

# Translate (compile) rpylean into an rpylean-c binary.
translate *ARGS:
    "{{ pypy }}" "{{ rpython }}" {{ ARGS }} "{{ target }}"

# Run rpylean's (untranslated) tests.
test *ARGS=tests:
    "{{ pypy }}" "{{ pypy_checkout }}/pytest.py" {{ ARGS }}
