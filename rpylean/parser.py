from __future__ import print_function

from rpython.rlib.parsing.ebnfparse import parse_ebnf, make_parse_function
from rpython.rlib.parsing.tree import RPythonVisitor
import py

from rpylean import RPYLEAN_DIR

grammar = py.path.local(RPYLEAN_DIR).join("grammar.txt").read("rt")
regexs, rules, ToAST = parse_ebnf(grammar)
_parse = make_parse_function(regexs, rules, eof=True)


class Node(object):
    """
    An AST node.
    """

    def __eq__(self, other):
        return (
            self.__class__ == other.__class__ and
            self.__dict__ == other.__dict__
        )

    def __ne__(self, other):
        return not self == other

    def __repr__(self):
        contents = ("%s=%r" % (k, v) for k, v in self.__dict__.iteritems())
        return "<%s %s>" % (self.__class__.__name__, ", ".join(contents))


class File(Node):
    def __init__(self, version, items=None):
        if items is None:
            items = []
        self.version = version
        self.items = items

    def compile(self, context):
        for item in self.items:
            item.compile(context)


class Version(Node):
    def __init__(self, major, minor, patch):
        self.major = int(major)
        self.minor = int(minor)
        self.patch = int(patch)


class NameStr(Node):
    def __init__(self, nidx, parent_nidx, name):
        self.nidx = nidx
        self.parent_nidx = parent_nidx
        self.name = name

    def compile(self, environment):
        environment.register_name(self.nidx, self.parent_nidx, self.name)


class Universe(Node):
    pass


class UniverseParam(Universe):
    def __init__(self, uidx, nidx):
        self.uidx = uidx
        self.nidx = nidx

    def compile(self, environment):
        pass


class Expr(Node):
    pass


class BVar(Expr):
    def __init__(self, eidx, id):
        self.eidx = eidx
        self.id = id

    def compile(self, environment):
        pass


class Sort(Expr):
    def __init__(self, eidx, uidx):
        self.eidx = eidx
        self.uidx = uidx

    def compile(self, environment):
        # level = environment.levels[self.uidx]
        # environment.register_expr(self.eidx, level)
        pass


class Const(Expr):
    def __init__(self, eidx, nidx, uidxs):
        self.eidx = eidx
        self.nidx = nidx
        self.uidxs = uidxs

    def compile(self, environment):
        value = environment.names[self.nidx]
        environment.register_expr(self.eidx, value) 


class App(Expr):
    def __init__(self, eidx, fn_eidx, arg_eidx):
        self.eidx = eidx
        self.fn_eidx = fn_eidx
        self.arg_eidx = arg_eidx

    def compile(self, environment):
        pass


class Lambda(Expr):
    def __init__(self, eidx):
        self.eidx = eidx

    def compile(self, environment):
        pass


class ForAll(Expr):
    def __init__(self, eidx):
        self.eidx = eidx

    def compile(self, environment):
        pass


class Declaration(Node):
    def __init__(self, decl):
        self.decl = decl

    def compile(self, environment):
        pass


class Definition(Node):
    pass


class Theorem(Node):
    pass


class Inductive(Node):
    pass


class Constructor(Node):
    pass


class Recursor(Node):
    pass


class RecRule(Node):
    def compile(self, environment):
        pass


class Transformer(RPythonVisitor):
    def dispatch(self, node):
        return getattr(self, "visit_%s" % node.symbol)(node)

    def visit_file(self, node):
        version = self.dispatch(node.children[0])
        return File(
            version=version,
            items=[self.dispatch(each) for each in node.children[1].children]
        )

    def visit_export_format_version(self, node):
        major, minor, patch = node.children
        return Version(
            major=major.additional_info,
            minor=minor.additional_info,
            patch=patch.additional_info,
        )

    def visit_item(self, node):
        item, = node.children
        return self.dispatch(item)

    def visit_name(self, node):
        nidx, kind, parent_nidx, id = node.children
        if kind.additional_info == "#NS":
            return NameStr(
                nidx=nidx.children[0].additional_info,
                parent_nidx=parent_nidx.children[0].additional_info,
                name=id,
            )
        elif kind.additional_info == "#NI":
            assert False, "implement #NI"
        else:
            assert False, "unknown name kind: " + kind.additional_info

    def visit_universe(self, node):
        kind = node.children[1]
        if kind.additional_info == "#UP":
            uidx, _, nidx = node.children
            return UniverseParam(
                uidx=uidx.children[0].additional_info,
                nidx=nidx.children[0].additional_info,
            )
        else:
            assert False, "unknown name kind: " + kind.additional_info

    def visit_expr(self, node):
        eidx = node.children[0].children[0].additional_info
        kind = node.children[1]
        if kind.additional_info == "#EV":
            _, _, id = node.children
            return BVar(eidx=eidx, id=id)
        elif kind.additional_info == "#ES":
            _, _, uidx = node.children
            return Sort(
                eidx=eidx,
                uidx=uidx.children[0].additional_info,
            )
        elif kind.additional_info == "#EC":
            nidx = node.children[2].children[0].additional_info
            return Const(
                eidx=eidx,
                nidx=nidx,
                uidxs=[
                    uidx.children[0].additional_info
                    for uidx in node.children[3:]
                ],
            )
        elif kind.additional_info == "#EA":
            _, _, fn_eidx, arg_eidx = node.children
            return App(
                eidx=eidx,
                fn_eidx=fn_eidx.children[0].additional_info,
                arg_eidx=arg_eidx.children[0].additional_info,
            )
        elif kind.additional_info == "#EL":
            # XXX: Implement me
            return Lambda(
                eidx=eidx,
            )
        elif kind.additional_info == "#EP":
            # XXX: Implement me
            return ForAll(eidx=eidx)
        else:
            assert False, "unknown expr kind: " + kind.additional_info

    def visit_declaration(self, node):
        child, = node.children
        return Declaration(self.dispatch(child))

    def visit_definition(self, node):
        # XXX: Implement me
        return Definition()

    def visit_theorem(self, node):
        # XXX: Implement me
        return Theorem()

    def visit_inductive(self, node):
        # XXX: Implement me
        return Inductive()

    def visit_constructor(self, node):
        # XXX: Implement me
        return Constructor()

    def visit_recursor(self, node):
        # XXX: Implement me
        return Recursor()

    def visit_recrule(self, node):
        # XXX: Implement me
        return RecRule()


transformer = Transformer()


def parse(source, transformer=transformer):
    ast = ToAST().transform(_parse(source))
    return transformer.visit_file(ast)
