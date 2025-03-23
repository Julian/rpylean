from rpylean.interpreter import interpret
from tests import examples

def test_interpret_basic():
    source = examples.export("Basic")
    interpret(source)

def test_interpet_sepxr():
    source = examples.export("Sexpr")
    interpret(source)
