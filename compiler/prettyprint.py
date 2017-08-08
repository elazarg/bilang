import nodes

from generated.visitor import NodeVisitor


class Printer(NodeVisitor[str]):

    def __init__(self):
        self.depth = 0

    def visit_ExpressionStatement(self, n: nodes.ExpressionStatement) -> str:
        return self.visit(n.value)

    def visit_Declare(self, n: nodes.Declare) -> str:
        return f'declare {n.declaration} by {self.args(n.participants)}'

    def visit_Pay(self, n: nodes.Pay) -> str:
        return f'pay {self.visit(n.name)} {self.args(n.args)}'

    def visit_Require(self, n: nodes.Require) -> str:
        return f'require {self.visit(n.test)}'

    def args(self, args) -> str:
        return ", ".join(self.visit(arg) for arg in args)

    def visit_VarDecl(self, n: nodes.VarDecl) -> str:
        init = ''
        if n.init is not None:
            init = ' = ' + self.visit(n.init)
        return f'{"".join(q + " " for q in n.qualifiers)}{n.type} {self.visit(n.name)}{init}'

    def visit_Assign(self, n: nodes.Assign) -> str:
        return f'{self.visit(n.name)} = {self.visit(n.value)}'

    def visit_ParallelJoin(self, n: nodes.ParallelJoin) -> str:
        return 'join ' + ' '.join(f'{self.visit(item)}' for item in n.items)

    def visit_ParallelWait(self, n: nodes.ParallelWait) -> str:
        return 'wait ' + ' '.join(f'{self.visit(item)}' for item in n.items)

    def visit_JoinItem(self, node: nodes.JoinItem) -> str:
        if node.var is not None:
            return f'{self.visit(node.tag)} as {self.visit(node.var)}'
        else:
            return f'{self.visit(node.tag)}'

    def visit_AwaitItem(self, node: nodes.AwaitItem) -> str:
        return f'{self.visit(node.to)}.{node.attr}'

    def visit_Struct(self, n: nodes.Struct) -> str:
        return f'Struct {n.name}{self.block(n.fields)}'

    def visit_With(self, n: nodes.With) -> str:
        return f'with {self.visit(n.context)} as {n.var}{self.block(n.body)}'

    def visit_While(self, n: nodes.While) -> str:
        return f'while {self.visit(n.test)}{self.block(n.body)}'

    def visit_IfElse(self, n: nodes.IfElse) -> str:
        return f'if {self.visit(n.test)}{self.block(n.body)}else{self.block(n.orelse)}'

    def visit_Session(self, n: nodes.Session) -> str:
        return f'session { self.visit(n.name)}{self.block(n.body)}'

    def block(self, *blocks: list) -> str:
        self.depth += 1
        res = ':\n'
        for block in blocks:
            for cmd in block:
                res += '    ' * self.depth + self.visit(cmd) + '\n'
        self.depth -= 1
        return res

    def visit_Continue(self, n: nodes.Continue) -> str:
        return 'continue'

    def visit_Break(self, n: nodes.Break) -> str:
        return 'break'

    def visit_VarName(self, node: nodes.VarName) -> str:
        return node.id

    def visit_Call(self, n: nodes.Call) -> str:
        return f'{self.visit(n.func)}({", ".join(self.visit(arg) for arg in n.args)})'

    def visit_Const(self, n: nodes.Const) -> str:
        return repr(n.n)

    def visit_IfExp(self, n: nodes.IfExp) -> str:
        return f'{self.visit(n.test)} ? {self.visit(n.body)} : {self.visit(n.orelse)}'

    def visit_Attribute(self, n: nodes.Attribute) -> str:
        return f'{self.visit(n.value)}.{n.attr}'

    def visit_BinOp(self, n: nodes.BinOp) -> str:
        return f'({self.visit(n.left)} {n.op} {self.visit(n.right)})'

    def visit_UnaryOp(self, n: nodes.UnaryOp) -> str:
        return f'({n.op} {self.visit(n.operand)})'

    def visit_Subscript(self, n: nodes.Subscript) -> str:
        return f'{self.visit(n.value)}[{self.visit(n.index)}]'

    def visit_LvalVar(self, node: nodes.LvalVar) -> str:
        return node.id

    def visit_LvalAttr(self, node: nodes.LvalAttr) -> str:
        return f'{self.visit(node.value)}.{node.attr}'
