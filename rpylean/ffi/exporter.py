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
  `W_Const` reference it uses (`_dump_deps`), then emit the constant
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
    W_Constructor,
    W_Inductive,
    W_LevelZero,
    W_Recursor,
    name_dict,
)
from rpylean.parser import EXPORT_VERSION
from rpython.rlib.objectmodel import compute_unique_id


META_LINE = (
    '{"meta":{"exporter":{"name":"rpylean","version":"0"},'
    '"format":{"version":"%s"}}}\n' % EXPORT_VERSION
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
        # Identity-keyed dedup. The FFI walker hash-cons Expr/Level
        # subtrees by Lean pointer; compute_unique_id is stable for
        # the whole export.
        self._level_ids = {}    # compute_unique_id(level) → level_id
        self._expr_ids = {}     # compute_unique_id(expr) → expr_id
        # Filled in by `_index_inductive_members` before the first
        # `dump_constant` call.
        self._induct_for_ctor = name_dict()     # ctor_name → induct_name
        self._ctors_of = name_dict()            # induct_name → [ctor_name]
        self._recs_of = name_dict()             # induct_name → [rec_name]
        self._indexed = False

    # ---- registration -------------------------------------------------

    def register(self, decl):
        """Add a walked declaration to the export pool.

        Must be called for every constant before `dump_all`."""
        self.decls[decl.name] = decl

    def emit_meta(self):
        self.stream.write(META_LINE)

    def quote(self, s):
        """JSON-quote `s` for embedding inside an export record. Used
        by `W_LitStr.emit_to` / `W_LitNat.emit_to` (and `_name_id`)."""
        return _json_string(s)

    def dump_all(self):
        """Emit every registered declaration in dependency order."""
        self._index_inductive_members()
        # Drive emission in registration order so the choice of "root"
        # constants is deterministic; deps come out before each root.
        for name in self.decls:
            self.dump_constant(self.decls[name])

    def _index_inductive_members(self):
        if self._indexed:
            return
        self._indexed = True
        # The walker doesn't yet store `induct` on ctors or the ctors
        # list on inductives, so we recover the mapping here by routing
        # each ctor to the inductive (in the registered pool) whose
        # mutual `names` list contains the ctor's dotted-name parent.
        for name in self.decls:
            decl = self.decls[name]
            kind = decl.w_kind
            if isinstance(kind, W_Constructor):
                induct = self._infer_ctor_induct(name)
                if induct is not None and induct in self.decls:
                    ind_decl = self.decls[induct]
                    if isinstance(ind_decl.w_kind, W_Inductive):
                        self._induct_for_ctor[name] = induct
                        if induct not in self._ctors_of:
                            self._ctors_of[induct] = []
                        self._ctors_of[induct].append(name)
            elif isinstance(kind, W_Recursor):
                for induct in kind.names:
                    if induct in self.decls:
                        if induct not in self._recs_of:
                            self._recs_of[induct] = []
                        self._recs_of[induct].append(name)

    def _infer_ctor_induct(self, ctor_name):
        parts = ctor_name.components
        if len(parts) <= 1:
            return None
        return Name(parts[:-1])

    # ---- dump_constant: dispatch + dep walk ----------------------------

    def dump_constant(self, decl):
        if decl.name in self._visited:
            return
        decl.w_kind.dump_to(self, decl)

    def _dump_deps(self, expr):
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
        parts = name.components
        parent = Name(parts[:-1]) if parts else Name.ANONYMOUS
        parent_id = self.name_id(parent)
        nid = self._next_name
        self._next_name += 1
        self._names[name] = nid
        last = parts[-1]
        if isinstance(last, int):
            payload = '{"pre":%d,"i":%d}' % (parent_id, last)
            self.stream.write('{"in":%d,"num":%s}\n' % (nid, payload))
        else:
            payload = '{"pre":%d,"str":%s}' % (parent_id, _json_string(last))
            self.stream.write('{"in":%d,"str":%s}\n' % (nid, payload))
        return nid

    def level_id(self, level):
        if isinstance(level, W_LevelZero):
            return 0
        uid = compute_unique_id(level)
        cached = self._level_ids.get(uid, -1)
        if cached != -1:
            return cached
        lid = level.emit_to(self)
        self._level_ids[uid] = lid
        return lid

    def expr_id(self, expr):
        uid = compute_unique_id(expr)
        cached = self._expr_ids.get(uid, -1)
        if cached != -1:
            return cached
        eid = expr.emit_to(self)
        self._expr_ids[uid] = eid
        return eid

    # ---- declaration emit ---------------------------------------------

    def _level_param_ids(self, names):
        return [self.name_id(n) for n in names]

    def _ids_list(self, ids):
        return "[" + ",".join([str(i) for i in ids]) + "]"

    def _emit_axiom(self, decl):
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        self.stream.write(
            '{"axiom":{"name":%d,"levelParams":%s,"type":%d,'
            '"isUnsafe":false}}\n'
            % (nid, self._ids_list(levels), tid),
        )

    def _emit_def(self, decl, value, hint):
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        vid = self.expr_id(value)
        self.stream.write(
            '{"def":{"name":%d,"levelParams":%s,"type":%d,'
            '"value":%d,"hints":%s,"safety":"safe","all":[%d]}}\n'
            % (nid, self._ids_list(levels), tid, vid,
               self._hint_json(hint), nid),
        )

    def _emit_thm(self, decl, value):
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        vid = self.expr_id(value)
        self.stream.write(
            '{"thm":{"name":%d,"levelParams":%s,"type":%d,'
            '"value":%d,"all":[%d]}}\n'
            % (nid, self._ids_list(levels), tid, vid, nid),
        )

    def _emit_opaque(self, decl, value):
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        vid = self.expr_id(value)
        self.stream.write(
            '{"opaque":{"name":%d,"levelParams":%s,"type":%d,'
            '"value":%d,"isUnsafe":false,"all":[%d]}}\n'
            % (nid, self._ids_list(levels), tid, vid, nid),
        )

    def _hint_json(self, hint):
        if hint == HINT_OPAQUE:
            return '"opaque"'
        if hint == HINT_ABBREV:
            return '"abbrev"'
        return '{"regular":%d}' % hint

    # ---- inductive blocks ---------------------------------------------

    def _dump_inductive_group(self, ind_decl):
        kind = ind_decl.w_kind
        assert isinstance(kind, W_Inductive)

        # Mark all mutual block members visited up front so deps cycling
        # back through any of them short-circuit.
        for n in kind.names:
            self._visited[n] = True

        ctor_pairs = []  # list of (induct_name, decl)
        rec_decls = []
        for n in kind.names:
            for cname in self._ctors_of.get(n, []):
                cd = self.decls.get(cname, None)
                if cd is not None:
                    self._visited[cname] = True
                    ctor_pairs.append((n, cd))
        for n in kind.names:
            for rname in self._recs_of.get(n, []):
                rd = self.decls.get(rname, None)
                if rd is not None:
                    self._visited[rname] = True
                    rec_decls.append(rd)

        for n in kind.names:
            d = self.decls.get(n, None)
            if d is not None:
                self._dump_deps(d.type)
        for (_n, cd) in ctor_pairs:
            self._dump_deps(cd.type)
        for rd in rec_decls:
            self._dump_deps(rd.type)
            rkind = rd.w_kind
            assert isinstance(rkind, W_Recursor)
            for rule in rkind.rules:
                self._dump_deps(rule.rhs)

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
            '{"inductive":{"types":[%s],"ctors":[%s],"recs":[%s]}}\n'
            % (",".join(type_records), ",".join(ctor_records),
               ",".join(rec_records)),
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
            '{"name":%d,"levelParams":%s,"type":%d,'
            '"numParams":%d,"numIndices":%d,"all":%s,"ctors":%s,'
            '"numNested":%d,"isRec":%s,"isUnsafe":false,'
            '"isReflexive":%s}'
            % (nid, self._ids_list(levels), tid,
               kind.num_params, kind.num_indices, all_ids, ctor_ids,
               kind.num_nested,
               "true" if kind.is_recursive else "false",
               "true" if kind.is_reflexive else "false")
        )

    def _constructor_val_json(self, decl, induct_name):
        kind = decl.w_kind
        assert isinstance(kind, W_Constructor)
        nid = self.name_id(decl.name)
        levels = self._level_param_ids(decl.levels)
        tid = self.expr_id(decl.type)
        induct_id = self.name_id(induct_name)
        return (
            '{"name":%d,"levelParams":%s,"type":%d,'
            '"induct":%d,"cidx":0,"numParams":%d,"numFields":%d,'
            '"isUnsafe":false}'
            % (nid, self._ids_list(levels), tid, induct_id,
               kind.num_params, kind.num_fields)
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
            '{"name":%d,"levelParams":%s,"type":%d,'
            '"all":%s,"numParams":%d,"numIndices":%d,'
            '"numMotives":%d,"numMinors":%d,'
            '"rules":[%s],"k":%s,"isUnsafe":false}'
            % (nid, self._ids_list(levels), tid, all_ids,
               kind.num_params, kind.num_indices,
               kind.num_motives, kind.num_minors,
               ",".join(rule_parts),
               "true" if kind.k else "false")
        )
