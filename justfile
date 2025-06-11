set dotenv-required

pypy := env('PYPY', 'pypy')
pypy_checkout := env('PYPY_CHECKOUT')
rpython := pypy_checkout / "rpython/bin/rpython"

package := justfile_directory() / "rpylean"
tests := justfile_directory() / "tests"
examples := tests / "examples"
target := justfile_directory() / "targetrpylean.py"

translated := justfile_directory() / "rpylean-c"
translated_tests := justfile_directory() / "translated-tests"

# Run rpylean (untranslated) with any extra arguments.
rpylean *ARGS:
    PYTHONPATH="{{ pypy_checkout }}/" "{{ pypy }}" -m rpylean {{ ARGS }}

# Run the rpylean REPL untranslated on an example.
example name:
    @just rpylean repl $(find "{{ examples }}" -iname "{{ name }}")/export

# Run a PyPy REPL with rpylean imported.
pypy $RPYLEAN_EXAMPLE='' *ARGS:
    PYTHONPATH="{{ pypy_checkout }}:{{ justfile_directory() }}" "{{ pypy }}" $@ -i "{{ package }}/_pypy_repl.py"

# Run the translated rpylean REPL under rlwrap.
repl *ARGS:
    rlwrap "{{ translated }}" repl {{ ARGS }}

# Run lean4export with the provided arguments.
lean4export *ARGS:
    lake --dir "${LEAN4EXPORT_CHECKOUT}" exe lean4export {{ ARGS }}

# Run lean4export on some self-contained source code in a single file.
export-simple path:
    olean_output_dir=$(mktemp -d); \
    lean -o "$olean_output_dir/JustfileTemporary.olean" "{{ path }}" && \
    LEAN_PATH=$olean_output_dir just lean4export JustfileTemporary; \
    rm "$olean_output_dir/JustfileTemporary.olean"; \
    rmdir "$olean_output_dir"

# Translate (compile) rpylean into an rpylean-c binary.
translate *ARGS:
    "{{ pypy }}" "{{ rpython }}" {{ ARGS }} "{{ target }}"

# Run rpylean's (untranslated) tests.
test *ARGS=tests:
    "{{ pypy }}" "{{ pypy_checkout }}/pytest.py" {{ ARGS }}

# Run rpylean's translated tests.
test-translated *ARGS=translated_tests:
    "{{ pypy }}" "{{ pypy_checkout }}/pytest.py" {{ ARGS }}
