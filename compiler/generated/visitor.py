from typing import TypeVar, Generic, Sequence, Union, Any
from nodes import Exp, Lvalue, VarDecl, VarName, With, Parallel, BinOp, AwaitItem, LvalAttr, Session, Const, Pay, LvalList, Call, Require, Break, IfElse, Subscript, TypeName, Attribute, UnaryOp, While, IfExp, Struct, Declare, Continue, LvalVar, JoinItem, ExpressionStatement, Assign

_T = TypeVar('_T')
_Q = TypeVar('_Q')


class Visitor(Generic[_T, _Q]):
    def visit(self, node) -> _T:
        return getattr(self, 'visit_' + type(node).__name__)(node)


class ExpVisitor(Generic[_T], Visitor[Exp, _T]):
    
    def visit_VarName(self, node: VarName) -> _T:
        raise NotImplementedError

    def visit_Call(self, node: Call) -> _T:
        raise NotImplementedError

    def visit_BinOp(self, node: BinOp) -> _T:
        raise NotImplementedError

    def visit_UnaryOp(self, node: UnaryOp) -> _T:
        raise NotImplementedError

    def visit_IfExp(self, node: IfExp) -> _T:
        raise NotImplementedError

    def visit_Const(self, node: Const) -> _T:
        raise NotImplementedError

    def visit_Attribute(self, node: Attribute) -> _T:
        raise NotImplementedError

    def visit_Subscript(self, node: Subscript) -> _T:
        raise NotImplementedError


class LvalVisitor(Generic[_T], Visitor[Lvalue, _T]):
    
    def visit_LvalVar(self, node: LvalVar) -> _T:
        raise NotImplementedError

    def visit_LvalAttr(self, node: LvalAttr) -> _T:
        raise NotImplementedError


class StmtVisitor(Generic[_T], Visitor[Any, _T]):
    
    def visit_TypeName(self, node: TypeName) -> _T:
        raise NotImplementedError

    def visit_LvalList(self, node: LvalList) -> _T:
        raise NotImplementedError

    def visit_Session(self, node: Session) -> _T:
        raise NotImplementedError

    def visit_VarDecl(self, node: VarDecl) -> _T:
        raise NotImplementedError

    def visit_Struct(self, node: Struct) -> _T:
        raise NotImplementedError

    def visit_Assign(self, node: Assign) -> _T:
        raise NotImplementedError

    def visit_Declare(self, node: Declare) -> _T:
        raise NotImplementedError

    def visit_Require(self, node: Require) -> _T:
        raise NotImplementedError

    def visit_Pay(self, node: Pay) -> _T:
        raise NotImplementedError

    def visit_ExpressionStatement(self, node: ExpressionStatement) -> _T:
        raise NotImplementedError

    def visit_JoinItem(self, node: JoinItem) -> _T:
        raise NotImplementedError

    def visit_AwaitItem(self, node: AwaitItem) -> _T:
        raise NotImplementedError

    def visit_Parallel(self, node: Parallel) -> _T:
        raise NotImplementedError

    def visit_IfElse(self, node: IfElse) -> _T:
        raise NotImplementedError

    def visit_While(self, node: While) -> _T:
        raise NotImplementedError

    def visit_Continue(self, node: Continue) -> _T:
        raise NotImplementedError

    def visit_Break(self, node: Break) -> _T:
        raise NotImplementedError

    def visit_With(self, node: With) -> _T:
        raise NotImplementedError


class NodeVisitor(Generic[_T], ExpVisitor[_T], StmtVisitor[_T], LvalVisitor[_T]):
    pass
