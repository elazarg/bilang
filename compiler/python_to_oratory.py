import ast
import nodes as ot

import typing as tt


class Translator(ast.NodeVisitor):
    def visit_AsyncFunctionDef(self, d: ast.AsyncFunctionDef) -> ot.Session:
        return ot.Session([self.visit(stmt) for stmt in d.body])

    def visit_Assign(self, n: ast.Assign) -> tt.Union[ot.Assign, ot.ParallelJoin]:
        assert len(n.targets) == 1
        target = n.targets[0]
        if isinstance(n.value, ast.Await):
            expr = n.value.value
            if isinstance(target, ast.Tuple):
                targets = target.elts
                rvals = expr.elts
                if len(rvals) != len(targets):
                    raise SyntaxWarning
                elts = list(zip(targets, rvals))
            else:
                assert isinstance(expr, ast.Name)
                assert isinstance(target, ast.Name)
                elts = [(expr, target)]
            return ot.ParallelJoin([ot.JoinItem(self.visit(t), self.visit(r))
                                    for t, r in elts])
        assert isinstance(target, ast.Name)
        return ot.Assign(target.id, n.value)

    def visit_AugAssign(self, n: ast.AugAssign) -> ot.Assign:
        return ot.Assign(n.target, ast.BinOp(n.op, n.target, n.value))

    def visit_AnnAssign(self, s: ast.AnnAssign) -> ot.VarDecl:
        qualifiers, t = parse_annotation(s.annotation)
        return ot.VarDecl(name=self.visit(s.target),
                          type=t,
                          init=s.value and self.visit(s.value),
                          qualifiers=qualifiers)

    def visit_ClassDef(self, cls: ast.ClassDef) -> ot.Struct:
        fields: tt.List[ot.VarDecl] = []
        reqs: tt.List[ot.Require] = []
        for pstmt in cls.body:
            stmt = self.visit(pstmt)
            if isinstance(stmt, ot.VarDecl):
                fields.append(stmt)
            elif isinstance(stmt, ot.Require):
                reqs.append(stmt)
            else:
                raise SyntaxError(stmt)
        return ot.Struct(cls.name, fields, reqs)

    def visit_Expr(self, body: ast.Expr) -> tt.Union[ot.Require, ot.Declare, ot.Pay, ot.ParallelWait, ot.ExpressionStatement]:
        expr = body.value
        if isinstance(expr, ast.Call) and isinstance(expr.func, ast.Name):
            call = expr
            name = call.func.id
            if name == 'require':
                [arg] = call.args
                return ot.Require(self.visit(arg))
            if name == 'declare':
                arg, *args = call.args
                assert isinstance(arg, ast.Str)
                return ot.Declare(arg.s, args)
            if name == 'pay':
                assert len(call.args) >= 2
                to, *args = call.args
                assert isinstance(to, ast.Name), to
                return ot.Pay(self.visit(to), [self.visit(arg) for arg in args])
        elif isinstance(expr, ast.Await):
            if isinstance(expr.value, ast.Tuple):
                elts = expr.value.elts
            else:
                assert isinstance(expr.value, ast.Attribute)
                elts = [expr.value]
            return ot.ParallelWait([ot.AwaitItem(self.visit(att.value), att.attr)
                                    for att in elts])
        return ot.ExpressionStatement(body)

    def visit_While(self, w: ast.While):
        return ot.While(w.test, w.body)

    def visit_With(self, w: ast.With):
        [item] = w.items[0]
        return ot.With(item.context, item.optional_var, w.body)

    def visit_Break(self, c): return ot.Break

    def visit_Continue(self, c): return ot.Continue

    def visit_Attribute(self, n: ast.Attribute) -> ot.Attribute:
        return ot.Attribute(self.visit(n.value), n.attr)

    def visit_Name(self, node: ast.Name) -> str:
        return node.id

    def visit_Num(self, node: ast.Num) -> ot.Const:
        return ot.Const(node.n)

    def visit_Str(self, node: ast.Str) -> ot.Const:
        return ot.Const(node.s)

    def visit_BoolOp(self, n: ast.BoolOp) -> ot.BinOp:
        left, right = n.values
        return self.handle_binop(left, n.op, right)

    def visit_Compare(self, n: ast.Compare) -> ot.BinOp:
        [right] = n.comparators
        [op] = n.ops
        return self.handle_binop(n.left, op, right)

    def visit_BinOp(self, n: ast.BinOp):
        return self.handle_binop(n.left, n.op, n.right)

    def handle_binop(self, left, op, right):
        return ot.BinOp(self.visit(left), self.visit(op), self.visit(right))

    def visit_UnaryOp(self, n):
        return ot.UnaryOp(self.visit(n.op), self.visit(n.operand))

    def visit_Call(self, node: ast.Call):
        assert len(node.keywords) == 0
        return ot.Call(self.visit(node.func), [self.visit(a) for a in node.args])

    def visit_IfExp(self, n: ast.IfExp):
        return ot.IfExp(self.visit(n.test), self.visit(n.body), self.visit(n.orelse))


def parse_annotation(ann: ast.Expression) -> tt.Tuple[tt.Sequence[str], ot.TypeName]:
    seq = []
    while isinstance(ann, ast.Subscript):
        assert isinstance(ann.value, ast.Name), ann.value
        seq.append(ann.value.id)
        ann = ann.slice.value
    assert isinstance(ann, ast.Name), ann
    return seq, ann.id


def translate(defn: ast.AsyncFunctionDef) -> ot.Session:
    slv = Translator()
    return slv.visit_AsyncFunctionDef(defn)


def parse_examples(code: str) -> None:
    node = ast.parse(code)
    for defn in node.body:
        if isinstance(defn, ast.AsyncFunctionDef):
            print(translate(defn))


if __name__ == '__main__':
    with open('examples.py') as f:
        parse_examples(f.read())
