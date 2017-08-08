from typing import Optional, Sequence

from generated.visitor import StmtVisitor
import nodes


def infer_stype(s: nodes.Session) -> str:
    return SessionInferenceVisitor().visit(s)


class SessionInferenceVisitor(StmtVisitor[Optional[str]]):
    depth: int = 0

    def __init__(self) -> None:
        self.depth = 0

    def visit_Session(self, n: nodes.Session) -> str:
        return f'global protocol {n.name.id}(public role S) {self.block(n.body)}'

    def visit_With(self, n: nodes.With) -> str:
        pass

    def parallel(self, nitems: Sequence) -> str:
        if len(nitems) == 1:
            return self.visit(nitems[0])
        actions = [self.visit(item) for item in nitems]
        res = ''
        for action in actions:
            res += 'par ' if not res else '} and '
            if action is not None:
                self.depth += 1
                res += '{\n'
                res += '    ' * self.depth + action + '\n'
                self.depth -= 1
                res += '    ' * self.depth
        res += '}'
        return res

    def visit_Parallel(self, n: nodes.Parallel) -> str:
        return self.parallel(n.items)

    def visit_AwaitItem(self, n: nodes.AwaitItem) -> str:
        res = ''
        # res += f'request_{n.attr}() from S to {n.to.id}; '
        res += f'receive({", ".join(self.visit(t) for t in n.types)}) from {n.to.id} to S;'
        return res

    def visit_IfElse(self, n: nodes.IfElse) -> str:
        return f'choice at S {self.block(n.body)} or {self.block(n.orelse)}'

    def visit_While(self, n: nodes.While) -> str:
        body = n.body + [nodes.Continue()]
        return f'rec loop {self.block(body)}'

    def visit_Continue(self, n: nodes.Continue) -> str:
        return 'loop;'

    def visit_Break(self, n: nodes.Break) -> None:
        return None

    def visit_VarName(self, n: nodes.VarName) -> None:
        return n.id

    def block(self, *blocks: list) -> str:
        self.depth += 1
        res = '{\n'
        for block in blocks:
            for cmd in block:
                action = self.visit(cmd)
                if action is not None:
                    res += '    ' * self.depth + action + '\n'
        self.depth -= 1
        res += '}'
        return res

    def visit_Assign(self, n: nodes.Assign) -> None:
        return None

    def visit_ExpressionStatement(self, n: nodes.ExpressionStatement) -> None:
        return None

    def visit_VarDecl(self, n: nodes.VarDecl) -> None:
        return None

    def visit_Pay(self, n: nodes.Pay) -> None:
        return None

    def visit_Require(self, n: nodes.Require) -> None:
        return None

    def visit_Declare(self, n: nodes.Declare) -> None:
        return None

    def visit_Struct(self, n: nodes.Struct) -> None:
        return None
