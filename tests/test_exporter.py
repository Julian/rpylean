"""
Tests for `rpylean.exporter` (lean4export 3.1.0 NDJSON emission).
"""

from StringIO import StringIO

from rpylean.environment import Environment
from rpylean.exporter import Exporter, json_escape, json_string
from rpylean.parser import from_export
from rpylean.objects import (
    HINT_ABBREV,
    HINT_OPAQUE,
    PROP,
    SAFETY_PARTIAL,
    SAFETY_SAFE,
    SAFETY_UNSAFE,
    TYPE,
    Binder,
    Name,
    W_BVar,
    W_ForAll,
    W_Lambda,
    W_RecRule,
)


def _export_all(decls):
    buf = StringIO()
    exporter = Exporter(buf)
    for d in decls:
        exporter.register(d)
    exporter.emit_meta()
    exporter.dump_all()
    return buf.getvalue()


def _export_named(decls, names):
    buf = StringIO()
    exporter = Exporter(buf)
    for d in decls:
        exporter.register(d)
    exporter.emit_meta()
    exporter.dump_named(names)
    return buf.getvalue()


class TestJSONEncoding(object):
    def test_json_string_quotes_and_escapes(self):
        assert json_string('a"b\\c\n\x01') == '"a\\"b\\\\c\\n\\u0001"'
        assert json_escape("plain") == "plain"


class TestDumpAll(object):
    def test_emits_safe_declarations_and_skips_unsafe_and_internal_roots(self):
        """Regression: `dump_all` must call `decl.is_unsafe()`, not test the method object."""
        pub = Name.simple("Pub").axiom(type=TYPE)
        unsafe_ax = Name.simple("Bad").axiom(type=TYPE, is_unsafe=True)
        internal_unused = Name.simple("_hidden").axiom(type=TYPE)
        internal_dep = Name.simple("_dep").axiom(type=TYPE)
        uses_internal = Name.simple("Uses").definition(
            type=TYPE, value=internal_dep.const(),
        )

        out = _export_all([
            pub, unsafe_ax, internal_unused, internal_dep, uses_internal,
        ])
        env = from_export(StringIO(out))

        assert Name.simple("Pub") in env.declarations
        assert Name.simple("Uses") in env.declarations
        # Internal dependency reachable from a public root is included.
        assert Name.simple("_dep") in env.declarations
        # Unsafe and unreachable internal roots are skipped.
        assert Name.simple("Bad") not in env.declarations
        assert Name.simple("_hidden") not in env.declarations

    def test_roundtrip_safe_declarations_and_hints(self):
        u = Name.simple("u")
        ax = Name.simple("A").axiom(type=TYPE)
        dfn = Name.simple("D").definition(
            type=TYPE, value=ax.const(), hint=HINT_ABBREV,
            safety=SAFETY_SAFE,
        )
        reg_def = Name.simple("R").definition(
            type=TYPE, value=ax.const(), hint=7,
            safety=SAFETY_PARTIAL,
        )
        op = Name.simple("O").opaque(type=TYPE, value=ax.const())
        thm = Name.simple("T").theorem(
            type=PROP,
            value=W_Lambda(Binder.default(Name.simple("p"), PROP), W_BVar(0)),
            levels=[u],
        )

        out = _export_all([ax, dfn, reg_def, op, thm])
        env = from_export(StringIO(out))

        assert set(env.declarations.keys()) == set([
            Name.simple("A"),
            Name.simple("D"),
            Name.simple("R"),
            Name.simple("O"),
            Name.simple("T"),
        ])
        assert env.declarations[Name.simple("D")].w_kind.hint == HINT_ABBREV
        assert env.declarations[Name.simple("R")].w_kind.hint == 7
        assert env.declarations[Name.simple("R")].safety == SAFETY_PARTIAL
        assert env.declarations[Name.simple("O")].w_kind.value is not None

    def test_inductive_unsafe_flag_preserved(self):
        """Inductives, constructors, and recursors must emit their actual `isUnsafe` flag."""
        unit_name = Name.simple("UUnit")
        mk_name = unit_name.child("mk")
        rec_name = unit_name.child("rec")

        mk = mk_name.constructor(
            type=unit_name.const(), num_params=0, num_fields=0, cidx=0,
            induct=unit_name, is_unsafe=True,
        )
        rec = rec_name.recursor(
            type=TYPE,
            rules=[W_RecRule(ctor_name=mk_name, num_fields=0, rhs=PROP)],
            num_motives=1, num_params=0, num_indices=0, num_minors=1,
            k=True, all=[unit_name], is_unsafe=True,
        )
        ind = unit_name.inductive(
            type=TYPE, constructors=[mk], recursors=[rec],
            ctor_names=[mk_name], is_unsafe=True,
        )

        out = _export_named([ind, mk, rec], [unit_name])
        ind_lines = [l for l in out.splitlines() if l.startswith('{"inductive":')]
        assert len(ind_lines) == 1
        assert '"isUnsafe":false' not in ind_lines[0]
        assert ind_lines[0].count('"isUnsafe":true') == 3

        env = from_export(StringIO(out))
        assert env.declarations[unit_name].is_unsafe()
        assert env.declarations[mk_name].is_unsafe()
        assert env.declarations[rec_name].is_unsafe()

    def test_safe_inductive_roundtrips_and_typechecks(self):
        unit_name = Name.simple("MyUnit")
        mk_name = unit_name.child("mk")
        rec_name = unit_name.child("rec")
        motive_var = Name.simple("motive")
        u = Name.simple("u")
        u_sort = u.as_level_param().sort()

        mk = mk_name.constructor(
            type=unit_name.const(), num_params=0, num_fields=0, cidx=0,
            induct=unit_name,
        )
        # motive : MyUnit -> Sort u
        motive_ty = W_ForAll(
            Binder.default(Name.simple("t"), unit_name.const()), u_sort,
        )
        # minor : motive MyUnit.mk
        minor_ty = W_BVar(0).app(mk_name.const())
        # rec : (motive : MyUnit -> Sort u) -> motive MyUnit.mk -> (t : MyUnit) -> motive t
        rec_ty = W_ForAll(
            Binder.implicit(motive_var, motive_ty),
            W_ForAll(
                Binder.default(Name.simple("mk"), minor_ty),
                W_ForAll(
                    Binder.default(Name.simple("t"), unit_name.const()),
                    W_BVar(2).app(W_BVar(0)),
                ),
            ),
        )
        rec_rhs = W_Lambda(
            Binder.implicit(motive_var, motive_ty),
            W_Lambda(
                Binder.default(Name.simple("mk"), minor_ty),
                W_BVar(0),
            ),
        )
        rec = rec_name.recursor(
            type=rec_ty,
            rules=[W_RecRule(ctor_name=mk_name, num_fields=0, rhs=rec_rhs)],
            num_motives=1, num_params=0, num_indices=0, num_minors=1,
            k=False, all=[unit_name], levels=[u],
        )
        ind = unit_name.inductive(
            type=TYPE, constructors=[mk], recursors=[rec],
            ctor_names=[mk_name],
        )

        out = _export_all([ind, mk, rec])
        env = from_export(StringIO(out))
        errors = list(env.type_check(env.all()))
        assert errors == [], [str(e) for e in errors]
        assert not env.declarations[unit_name].is_unsafe()
        assert not env.declarations[mk_name].is_unsafe()
        assert not env.declarations[rec_name].is_unsafe()

    def test_dump_named_emits_transitive_deps_in_order(self):
        a = Name.simple("A").axiom(type=TYPE)
        b = Name.simple("B").definition(type=TYPE, value=a.const(), hint=HINT_OPAQUE)
        c = Name.simple("C").axiom(type=TYPE)

        out = _export_named([a, b, c], [Name.simple("B")])
        env = from_export(StringIO(out))
        assert Name.simple("A") in env.declarations
        assert Name.simple("B") in env.declarations
        assert Name.simple("C") not in env.declarations
        assert list(env.type_check(env.all())) == []
