"""
Emit a `lean4export`-format NDJSON stream from rpylean's walked declarations.

The format is documented at
https://github.com/leanprover/lean4export/blob/master/format_ndjson.md
(version 3.1.0). Each line is a self-contained JSON record; names,
levels, and expressions are emitted with integer IDs and referenced
by those IDs from later records. Anonymous Name has id 0 reserved;
Level.zero has id 0 reserved.

The traversal strategy follows lean4export's `Export.lean`:

* Walk each constant in two phases — first emit every transitive
  `W_Const` reference it uses (`dump_deps`), then emit the constant
  itself. This produces a dependency-ordered file.
* When the constant is part of an inductive mutual block, emit the
  whole `{"inductive": {types, ctors, recs}}` record in place, after
  dumping deps for every member's type plus every recursor rule's
  rhs. Constructors and recursors encountered later are short-circuited
  through their parent inductive.

Cross-validation use:

    rpylean ffi export Init >/tmp/init-ffi.ndjson
    rpylean check /tmp/init-ffi.ndjson

If both halves of rpylean (the FFI walker + the NDJSON parser) agree
on a declaration's shape, the second command type-checks the same
env and produces the same diagnostics as `rpylean ffi check Init`.
"""
from __future__ import print_function

from rpylean.objects import (
    HINT_ABBREV,
    HINT_OPAQUE,
    Name,
    NumName,
    W_Constructor,
    W_Inductive,
    W_LevelZero,
    W_Recursor,
    name_dict,
    syntactic_eq,
)
from rpylean.parser import EXPORT_VERSION
from rpython.rlib.objectmodel import compute_unique_id, r_dict


def _level_dict():
    """A content-keyed `r_dict` mapping `W_Level` → int (level id).

    Matches `lean4export`'s `HashMap Level Nat`: structurally-equal
    levels collapse to one cache entry, even when they came from
    distinct Lean pointers.
    """
    def _eq(a, b):
        return syntactic_eq(a, b)

    def _hash(level):
        return level.hash()

    return r_dict(_eq, _hash)


def _expr_dict():
    """Same idea as `_level_dict`, but for `W_Expr` → int (expr id).

    Matches `lean4export`'s `HashMap Expr Nat`. Each W_Expr subclass
    sets a content-mixing `_hash` in its constructor; structurally-equal
    exprs from different Lean pointers collapse here.
    """
    def _eq(a, b):
        return syntactic_eq(a, b)

    def _hash(expr):
        return expr.hash()

    return r_dict(_eq, _hash)


try:
    from rpylean._version import __version__ as _RPYLEAN_VERSION
except ImportError:
    _RPYLEAN_VERSION = "unknown"


def _meta_line(lean_version, lean_githash):
    # Keys in `meta` go in alphabetical order to match `lean4export`'s
    # output (which inherits Lean's `Json.compress` key sort): exporter,
    # format, lean.
    return (
        '{"meta":{"exporter":{"name":"rpylean","version":"%s"},'
        '"format":{"version":"%s"},'
        '"lean":{"githash":"%s","version":"%s"}}}\n'
        % (_RPYLEAN_VERSION, EXPORT_VERSION, lean_githash, lean_version)
    )


def _json_string(s):
    """Quote `s` for JSON. Handles the bare minimum: backslash, quote,
    control bytes. Lean names are typically ASCII identifiers, so we
    don't worry about full Unicode escaping."""
    out = ['"']
    for ch in s:
        c = ord(ch)
        if ch == '\\':
            out.append('\\\\')
        elif ch == '"':
            out.append('\\"')
        elif ch == '\n':
            out.append('\\n')
        elif ch == '\r':
            out.append('\\r')
        elif ch == '\t':
            out.append('\\t')
        elif c < 0x20:
            h = "0123456789abcdef"
            out.append("\\u")
            out.append(h[(c >> 12) & 0xf])
            out.append(h[(c >> 8) & 0xf])
            out.append(h[(c >> 4) & 0xf])
            out.append(h[c & 0xf])
        else:
            out.append(ch)
    out.append('"')
    return "".join(out)


class Exporter(object):
    """
    Two-pass export: callers feed every walked W_Declaration via
    `register`, then call `dump_all` to drive the topological emit.

    Index assignment for Name/Level/Expr is per-export, and Expr/Level
    dedup relies on the FFI walker's pointer-cache (so shared subterms
    come back as the same rpylean object).
    """

    def __init__(self, stream):
        self.stream = stream
        self.decls = name_dict()                # name → W_Declaration
        self._visited = name_dict()             # name → True (emitted)
        self._names = name_dict()
        self._names[Name.ANONYMOUS] = 0
        self._next_name = 1
        self._next_level = 1
        self._next_expr = 0
        # Content-keyed (`lean4export`-style): structurally-equal
        # levels and exprs share an id even when they came from
        # distinct Lean pointers.
        self._level_ids = _level_dict()    # W_Level → level_id
        self._expr_ids = _expr_dict()      # W_Expr → expr_id
        # Filled in by `_index_inductive_members` before the first
        # `dump_constant` call.
        self._induct_for_ctor = name_dict()     # ctor_name → induct_name
        self._ctors_of = name_dict()            # induct_name → [ctor_name]
        self._recs_of = name_dict()             # induct_name → [rec_name]
        self._indexed = False
        # Set by the CLI via `set_lean_meta` before `emit_meta` so we
        # can include the Lean toolchain's own version + git hash.
        self._lean_version = ""
        self._lean_githash = ""

    # ---- registration -------------------------------------------------

    def register(self, decl):
        """Add a walked declaration to the export pool.

        Must be called for every constant before `dump_all`."""
        self.decls[decl.name] = decl

    def set_lean_meta(self, version, githash):
        """Record the Lean toolchain's version + git hash, to be
        included on the `"lean"` field of the meta line."""
        self._lean_version = version
        self._lean_githash = githash

    def emit_meta(self):
        self.stream.write(_meta_line(self._lean_version, self._lean_githash))

    def quote(self, s):
        """JSON-quote `s` for embedding inside an export record. Used
        by `W_LitStr.emit_to` / `W_LitNat.emit_to`."""
        return _json_string(s)

    # ---- visitor-facing API -------------------------------------------
    # The following methods form the contract that `W_*.dump_to` /
    # `W_*.emit_to` rely on. Public on purpose: the visitor classes
    # live in `rpylean.objects` and must be able to call into here
    # without poking underscored internals.

    def begin_decl(self, decl):
        """Mark `decl` visited and dump its type's transitive deps.

        Common preamble for every value-bearing declaration (axiom,
        def, thm, opaque) and the constructor-without-parent fallback.
        `W_Inductive` bypasses this — its block emit marks every
        mutual member at once."""
        self._visited[decl.name] = True
        self.dump_deps(decl.type)

    def mark_emitted(self, name):
        """Record `name` as already emitted, so subsequent
        `dump_constant` calls for it short-circuit. Used by
        `W_Inductive.dump_to` to mark every member of a mutual block
        (the inductives themselves plus their ctors and recursors)
        before recurring into dep walks that may cycle back."""
        self._visited[name] = True

    def ctors_of(self, ind_name):
        """The constructor names registered as belonging to `ind_name`."""
        return self._ctors_of.get(ind_name, [])

    def recs_of(self, ind_name):
        """The recursor names registered as targeting `ind_name`."""
        return self._recs_of.get(ind_name, [])

    def parent_inductive(self, ctor_name):
        """The inductive name a registered constructor belongs to, or
        `None` if the parent wasn't part of the export pool."""
        return self._induct_for_ctor.get(ctor_name, None)

    def next_expr_id(self):
        """Allocate the next sequential expression id."""
        eid = self._next_expr
        self._next_expr += 1
        return eid

    def next_level_id(self):
        """Allocate the next sequential level id."""
        lid = self._next_level
        self._next_level += 1
        return lid

    def dump_all(self):
        """Emit every registered declaration in dependency order.

        Skips two kinds of roots, matching `lean4export`'s defaults:

        * Internal names (`Name.is_internal`: any component starts
          with `_`) aren't used as roots, though they still appear
          when reachable from a non-internal root.
        * Unsafe-flagged declarations are skipped entirely;
          `lean4export` only includes them with `--export-unsafe`.
        """
        self._index_inductive_members()
        for name in self.decls:
            decl = self.decls[name]
            if name.is_internal:
                continue
            if decl.is_unsafe:
                continue
            self.dump_constant(decl)

    def dump_named(self, names):
        """Emit only the named declarations (and their transitive deps).

        The topological dep walk in `dump_constant` pulls in every
        referenced constant, so the output stays self-contained as long
        as those deps were registered."""
        self._index_inductive_members()
        for name in names:
            d = self.decls.get(name, None)
            if d is not None:
                self.dump_constant(d)

    def _index_inductive_members(self):
        if self._indexed:
            return
        self._indexed = True
        # Authoritative source-order ctors come from each inductive's
        # `ctor_names` field; the reverse ctor→induct map falls out of
        # that. Recursors don't store reverse links on the inductive,
        # so we still scan all recursors and append to `_recs_of`.
        for name in self.decls:
            decl = self.decls[name]
            kind = decl.w_kind
            if isinstance(kind, W_Inductive):
                self._ctors_of[name] = list(kind.ctor_names)
                for cname in kind.ctor_names:
                    self._induct_for_ctor[cname] = name
            elif isinstance(kind, W_Recursor):
                for induct in kind.names:
                    if induct in self.decls:
                        if induct not in self._recs_of:
                            self._recs_of[induct] = []
                        self._recs_of[induct].append(name)

    # ---- dump_constant: dispatch + dep walk ----------------------------

    def dump_constant(self, decl):
        if decl.name in self._visited:
            return
        decl.w_kind.dump_to(self, decl)

    def dump_deps(self, expr):
        names = []
        seen = name_dict()
        expr.collect_consts_into(names, seen)
        for n in names:
            d = self.decls.get(n, None)
            if d is not None:
                self.dump_constant(d)

    # ---- primitives ---------------------------------------------------

    def name_id(self, name):
        if name in self._names:
            return self._names[name]
        # Anonymous is pre-seeded at id 0 in __init__; getting here means
        # `name` is a StrName or NumName with a parent we need to emit first.
        parent_id = self.name_id(name.parent)
        nid = self._next_name
        self._next_name += 1
        self._names[name] = nid
        if isinstance(name, NumName):
            payload = '{"i":%s,"pre":%d}' % (name.idx.str(), parent_id)
            self.stream.write('{"in":%d,"num":%s}\n' % (nid, payload))
        else:
            payload = '{"pre":%d,"str":%s}' % (
                parent_id, _json_string(name.suffix),
            )
            self.stream.write('{"in":%d,"str":%s}\n' % (nid, payload))
        return nid

    def level_id(self, level):
        if isinstance(level, W_LevelZero):
            return 0
        cached = self._level_ids.get(level, -1)
        if cached != -1:
            return cached
        lid = level.emit_to(self)
        self._level_ids[level] = lid
        return lid

    def expr_id(self, expr):
        cached = self._expr_ids.get(expr, -1)
        if cached != -1:
            return cached
        eid = expr.emit_to(self)
        self._expr_ids[expr] = eid
        return eid

    # ---- declaration emit ---------------------------------------------

    def _level_param_ids(self, names):
        # Match `lean4export`'s `dumpUparams`: register each name, then
        # also emit each as a `Level.param` record up front, so the
        # output reads "name, param, name, param, ..." before any expr
        # starts referencing them. `Name.as_level_param()` is cached so the
        # `W_LevelParam` we materialise here is `is`-identical to the
        # one the walker handed `read_level` for `Lean.Level.param`;
        # the existing `compute_unique_id`-keyed dedup then handles
        # any later references for free.
        out = [self.name_id(n) for n in names]
        for n in names:
            self.level_id(n.as_level_param())
        return out

    def _ids_list(self, ids):
        return "[" + ",".join([str(i) for i in ids]) + "]"

    def emit_axiom(self, decl):
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        self.stream.write(
            '{"axiom":{"isUnsafe":false,"levelParams":%s,'
            '"name":%d,"type":%d}}\n'
            % (self._ids_list(levels), nid, tid),
        )

    def emit_quot(self, decl, kind):
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        self.stream.write(
            '{"quot":{"kind":"%s","levelParams":%s,"name":%d,"type":%d}}\n'
            % (kind, self._ids_list(levels), nid, tid),
        )

    def emit_def(self, decl, value, hint):
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        vid = self.expr_id(value)
        self.stream.write(
            '{"def":{"all":[%d],"hints":%s,"levelParams":%s,'
            '"name":%d,"safety":"safe","type":%d,"value":%d}}\n'
            % (nid, self._hint_json(hint), self._ids_list(levels),
               nid, tid, vid),
        )

    def emit_thm(self, decl, value):
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        vid = self.expr_id(value)
        self.stream.write(
            '{"thm":{"all":[%d],"levelParams":%s,"name":%d,'
            '"type":%d,"value":%d}}\n'
            % (nid, self._ids_list(levels), nid, tid, vid),
        )

    def emit_opaque(self, decl, value):
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        vid = self.expr_id(value)
        self.stream.write(
            '{"opaque":{"all":[%d],"isUnsafe":false,"levelParams":%s,'
            '"name":%d,"type":%d,"value":%d}}\n'
            % (nid, self._ids_list(levels), nid, tid, vid),
        )

    def _hint_json(self, hint):
        if hint == HINT_OPAQUE:
            return '"opaque"'
        if hint == HINT_ABBREV:
            return '"abbrev"'
        return '{"regular":%d}' % hint

    # ---- inductive blocks ---------------------------------------------

    def emit_inductive_block(self, ind_decl, ctor_pairs, rec_decls):
        """Format a single `{"inductive": {types, ctors, recs}}` record.

        Coordination — gathering ctor_pairs and rec_decls, marking
        mutual members visited, dumping deps — lives in
        `W_Inductive.dump_to`. This method only handles the JSON
        formatting."""
        kind = ind_decl.w_kind
        assert isinstance(kind, W_Inductive)

        type_records = []
        for n in kind.names:
            d = self.decls.get(n, ind_decl)
            type_records.append(self._inductive_val_json(d))

        ctor_records = []
        for (induct_name, cd) in ctor_pairs:
            ctor_records.append(self._constructor_val_json(cd, induct_name))

        rec_records = []
        for rd in rec_decls:
            rec_records.append(self._recursor_val_json(rd))

        self.stream.write(
            '{"inductive":{"ctors":[%s],"recs":[%s],"types":[%s]}}\n'
            % (",".join(ctor_records), ",".join(rec_records),
               ",".join(type_records)),
        )

    def _ctor_names_for(self, ind_name):
        out = []
        for cn in self._ctors_of.get(ind_name, []):
            out.append(self.name_id(cn))
        return out

    def _inductive_val_json(self, decl):
        kind = decl.w_kind
        assert isinstance(kind, W_Inductive)
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        all_ids = self._ids_list([self.name_id(n) for n in kind.names])
        ctor_ids = self._ids_list(self._ctor_names_for(decl.name))
        return (
            '{"all":%s,"ctors":%s,"isRec":%s,"isReflexive":%s,'
            '"isUnsafe":false,"levelParams":%s,"name":%d,'
            '"numIndices":%d,"numNested":%d,"numParams":%d,"type":%d}'
            % (all_ids, ctor_ids,
               "true" if kind.is_recursive else "false",
               "true" if kind.is_reflexive else "false",
               self._ids_list(levels), nid,
               kind.num_indices, kind.num_nested, kind.num_params, tid)
        )

    def _constructor_val_json(self, decl, induct_name):
        kind = decl.w_kind
        assert isinstance(kind, W_Constructor)
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        induct_id = self.name_id(induct_name)
        return (
            '{"cidx":%d,"induct":%d,"isUnsafe":false,"levelParams":%s,'
            '"name":%d,"numFields":%d,"numParams":%d,"type":%d}'
            % (kind.cidx, induct_id, self._ids_list(levels),
               nid, kind.num_fields, kind.num_params, tid)
        )

    def _recursor_val_json(self, decl):
        kind = decl.w_kind
        assert isinstance(kind, W_Recursor)
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        all_ids = self._ids_list([self.name_id(n) for n in kind.names])
        rule_parts = []
        for rule in kind.rules:
            ctor_id = self.name_id(rule.ctor_name)
            rhs_id = self.expr_id(rule.rhs)
            rule_parts.append(
                '{"ctor":%d,"nfields":%d,"rhs":%d}'
                % (ctor_id, rule.num_fields, rhs_id),
            )
        return (
            '{"all":%s,"isUnsafe":false,"k":%s,"levelParams":%s,'
            '"name":%d,"numIndices":%d,"numMinors":%d,"numMotives":%d,'
            '"numParams":%d,"rules":[%s],"type":%d}'
            % (all_ids,
               "true" if kind.k else "false",
               self._ids_list(levels), nid,
               kind.num_indices, kind.num_minors, kind.num_motives,
               kind.num_params, ",".join(rule_parts), tid)
        )
