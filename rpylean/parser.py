from __future__ import print_function

from rpython.rlib.parsing.ebnfparse import parse_ebnf, make_parse_function
from rpython.rlib.parsing.tree import RPythonVisitor
import py

from rpylean import RPYLEAN_DIR

grammar = py.path.local(RPYLEAN_DIR).join("grammar.txt").read("rt")
regexs, rules, ToAST = parse_ebnf(grammar)
_parse = make_parse_function(regexs, rules, eof=True)


def parse(source):
    ast = ToAST().transform(_parse(source))
    _, items = ast.children
    return items
