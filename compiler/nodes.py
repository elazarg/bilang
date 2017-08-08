from typing import NamedTuple, Sequence, Union


Block = Sequence['Statement']

# Pure expressions
Exp = Union['UnOp', 'BinOp', 'UnaryOp', 'Call', 'Subscript',
            'Attribute', 'IfExp', 'Const', 'VarName']


class VarName(NamedTuple):
    id: str

TypeName = VarName


class LvalVar(NamedTuple):
    id: str


class LvalList(NamedTuple):
    items: Sequence['Lvalue']


class LvalAttr(NamedTuple):
    value: Exp
    attr: str

Lvalue = Union[LvalVar, LvalAttr]


class Session(NamedTuple):
    name: LvalVar
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
    name: LvalVar
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
    var: LvalVar


class AwaitItem(NamedTuple):
    to: VarName
    targets: Sequence[Lvalue]
    types: Sequence[TypeName]


class Parallel(NamedTuple):
    items: Sequence[Union[JoinItem, AwaitItem]]


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
    var: LvalVar
    body: Block


Statement = Union[Assign, ExpressionStatement,
                  IfElse, While, With, Parallel,
                  Declare, Pay, Require,
                  Continue, Break]


class Call(NamedTuple):
    func: Exp
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
