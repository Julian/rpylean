from __future__ import print_function

from rpylean.parser import parse


class Environment:
    def __init__(self):
        self.names = {0: []}

    def __repr__(self):
        return "Environment()"

    def add(self, nidx, _):
        self.names[nidx] = _


def interpret(source):
    items = parse(source)

    env = Environment()

    for each in items.children:
        if each.children[0].symbol == "name":
            name_node = each.children[0]
            symbol = name_node.children[0].children[0]
            new_nidx = int(symbol.additional_info)
            parent_nidx = int(name_node.children[2].children[0].additional_info)
            parent = env.names[parent_nidx]

            name = name_node.children[3].additional_info
            env.add(new_nidx, parent + [name])

    print(env.names)
