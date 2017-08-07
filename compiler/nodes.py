from typing import NamedTuple, Sequence, Union


VarName = str

Block = Sequence['Statement']

# Pure expressions
Exp = Union['UnOp', 'BinOp', 'Call', 'Subscript', 'Attribute', 'IfExp', 'Const', 'VarName']


class Session(NamedTuple):
    body: Block


# Declarations

class VarDecl(NamedTuple):
    name: VarName
    type: str
    init: Exp
    qualifiers: Sequence[str]


class Struct(NamedTuple):
    name: VarName
    fields: Sequence[VarDecl]
    requirements: Sequence[Exp]


# Statements


class Assign(NamedTuple):
    name: VarName
    value: Exp


class Declare(NamedTuple):
    declaration: str
    participants: Sequence[int]


class Require(NamedTuple):
    test: Exp


class Pay(NamedTuple):
    name: VarName
    args: Sequence[str]


class ExpressionStatement(NamedTuple):
    value: Exp


class JoinItem(NamedTuple):
    tag: str
    var: VarName


class AwaitItem(NamedTuple):
    to: VarName
    attr: VarName


class ParallelJoin(NamedTuple):
    items: Sequence[JoinItem]


class ParallelWait(NamedTuple):
    items: Sequence[AwaitItem]


Parallel = Union[ParallelJoin, ParallelWait]


class IfElse(NamedTuple):
    test: Exp
    body: Block
    orelse: Block


class While(NamedTuple):
    test: Exp
    body: Block
    # No orelse


class Continue(NamedTuple):
    pass


class Break(NamedTuple):
    pass


class With(NamedTuple):
    context: Exp
    var: str
    body: Block


Statement = Union[Assign, ExpressionStatement,
                  Declare, Pay, Require,
                  ParallelJoin, ParallelWait]


class Call(NamedTuple):
    func: str
    args: Sequence[Exp]


class BinOp(NamedTuple):
    left: Exp
    op: str
    right: Exp


class UnaryOp(NamedTuple):
    op: str
    operand: Exp


class IfExp(NamedTuple):
    test: Exp
    body: Exp
    orelse: Exp


class Const(NamedTuple):
    n: object


class Attribute(NamedTuple):
    value: Exp
    attr: VarName


class Subscript(NamedTuple):
    value: VarName
    index: Exp


# # Visitor Generator


cls_fmt = '''
from typing import TypeVar, Generic
import {mod}

_T = TypeVar('_T')


class NodeVisitor(Generic(_T)):
    """
    """
    {defs}
'''

def_fmt = '''
    def visit_{name}(self, node: {mod}.{name}) -> _T:
        raise NotImplementedError
'''


def generate_visitor(vs):
    from os.path import basename
    mod = basename(__file__)[:-3]
    defs = ''.join(def_fmt.format(name=name, varname=name[0].lower(), mod=mod)
                   for name, v in vs.items()
                   if hasattr(v, '_fields'))
    return cls_fmt.format(defs=defs, mod=mod)

if __name__ == '__main__':
    with open('generated/visitor.py', 'w') as f:
        print(generate_visitor(vars()), file=f, end='')
