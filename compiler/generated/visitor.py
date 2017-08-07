
from typing import TypeVar, Generic
import nodes

_T = TypeVar('_T')


class NodeVisitor(Generic(_T)):
    """
    """
    
    def visit_Session(self, node: nodes.Session) -> _T:
        raise NotImplementedError

    def visit_VarDecl(self, node: nodes.VarDecl) -> _T:
        raise NotImplementedError

    def visit_Struct(self, node: nodes.Struct) -> _T:
        raise NotImplementedError

    def visit_Assign(self, node: nodes.Assign) -> _T:
        raise NotImplementedError

    def visit_Declare(self, node: nodes.Declare) -> _T:
        raise NotImplementedError

    def visit_Require(self, node: nodes.Require) -> _T:
        raise NotImplementedError

    def visit_Pay(self, node: nodes.Pay) -> _T:
        raise NotImplementedError

    def visit_ExpressionStatement(self, node: nodes.ExpressionStatement) -> _T:
        raise NotImplementedError

    def visit_JoinItem(self, node: nodes.JoinItem) -> _T:
        raise NotImplementedError

    def visit_AwaitItem(self, node: nodes.AwaitItem) -> _T:
        raise NotImplementedError

    def visit_ParallelJoin(self, node: nodes.ParallelJoin) -> _T:
        raise NotImplementedError

    def visit_ParallelWait(self, node: nodes.ParallelWait) -> _T:
        raise NotImplementedError

    def visit_IfElse(self, node: nodes.IfElse) -> _T:
        raise NotImplementedError

    def visit_While(self, node: nodes.While) -> _T:
        raise NotImplementedError

    def visit_Continue(self, node: nodes.Continue) -> _T:
        raise NotImplementedError

    def visit_Break(self, node: nodes.Break) -> _T:
        raise NotImplementedError

    def visit_With(self, node: nodes.With) -> _T:
        raise NotImplementedError

    def visit_Call(self, node: nodes.Call) -> _T:
        raise NotImplementedError

    def visit_BinOp(self, node: nodes.BinOp) -> _T:
        raise NotImplementedError

    def visit_UnaryOp(self, node: nodes.UnaryOp) -> _T:
        raise NotImplementedError

    def visit_IfExp(self, node: nodes.IfExp) -> _T:
        raise NotImplementedError

    def visit_Const(self, node: nodes.Const) -> _T:
        raise NotImplementedError

    def visit_Attribute(self, node: nodes.Attribute) -> _T:
        raise NotImplementedError

    def visit_Subscript(self, node: nodes.Subscript) -> _T:
        raise NotImplementedError

