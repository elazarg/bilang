import ast
import nodes as ot

import typing as tt


class Translator(ast.NodeVisitor):
    def visit_AsyncFunctionDef(self, d: ast.AsyncFunctionDef) -> ot.Session:
        return ot.Session(ot.LvalVar(d.name), [self.visit(stmt) for stmt in d.body])

    def visit_Assign(self, n: ast.Assign) -> tt.Union[ot.Assign, ot.Parallel]:
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
                elts = [(target, expr)]
            return self.parallel(elts)
        assert isinstance(target, ast.Name)
        return ot.Assign(self.visit(target), self.visit(n.value))

    def parallel(self, elts: tt.Sequence[tt.Tuple[ast.Expr, ast.Expr]]):
        items = []
        for target, expr in elts:
            if isinstance(expr, ast.Str):
                # Join
                items.append(ot.JoinItem(self.visit(expr), self.visit(target)))
            elif isinstance(expr, ast.Subscript):
                # Await
                type_arg = expr.slice.value
                if isinstance(type_arg, ast.Tuple):
                    assert isinstance(target, ast.List)
                    type_args = type_arg.elts
                    targets = target.elts
                else:
                    type_args = [type_arg]
                    targets = [target]
                items.append(ot.AwaitItem(self.visit(expr.value),
                                          [self.visit(t) for t in targets],
                                          [self.visit(a) for a in type_args]))
            else:
                assert False, expr
        return ot.Parallel(items)

    def visit_AugAssign(self, n: ast.AugAssign) -> ot.Assign:
        return ot.Assign(self.visit(n.target), ast.BinOp(n.op, n.target, n.value))

    def visit_AnnAssign(self, s: ast.AnnAssign) -> ot.VarDecl:
        qualifiers, t = parse_annotation(s.annotation)
        return ot.VarDecl(name=self.visit(s.target), type=t,
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

    def visit_Expr(self, body: ast.Expr) -> tt.Union[ot.Require, ot.Declare, ot.Pay, ot.Parallel, ot.ExpressionStatement]:
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
        return ot.ExpressionStatement(body)

    def visit_While(self, w: ast.While):
        return ot.While(w.test, w.body)

    def visit_With(self, w: ast.With):
        [item] = w.items[0]
        return ot.With(item.context, item.optional_var, w.body)

    def visit_Break(self, c):
        return ot.Break

    def visit_Continue(self, c):
        return ot.Continue

    def visit_Attribute(self, n: ast.Attribute) -> ot.Attribute:
        if isinstance(n.ctx, ast.Load):
            return ot.Attribute(self.visit(n.value), n.attr)
        else:
            return ot.LvalAttr(self.visit(n.value), n.attr)

    def visit_Name(self, n: ast.Name) -> tt.Union[ot.VarName, ot.LvalVar]:
        if isinstance(n.ctx, ast.Load):
            return ot.VarName(n.id)
        else:
            return ot.LvalVar(n.id)

    def visit_Num(self, node: ast.Num) -> ot.Const:
        return ot.Const(node.n)

    def visit_Str(self, node: ast.Str) -> ot.Const:
        return ot.Const(node.s)

    def visit_List(self, node: ast.Str) -> ot.Const:
        assert False

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

    def visit_And(self, n: ast.And): return '&&'
    def visit_Or(self, n: ast.Or): return '||'
    def visit_Add(self, n: ast.Add): return '+'
    def visit_Sub(self, n: ast.Sub): return '-'
    def visit_Mult(self, n: ast.Mult): return '*'
    def visit_MatMult(self, n: ast.MatMult): assert False
    def visit_Div(self, n: ast.Div): return '/'
    def visit_Mod(self, n: ast.Mod): return '%'
    def visit_Pow(self, n: ast.Pow):  assert False
    def visit_LShift(self, n: ast.LShift): return '<<'
    def visit_RShift(self, n: ast.RShift): return '>>'
    def visit_BitOr(self, n: ast.BitOr): return '|'
    def visit_BitXor(self, n: ast.BitXor): return '^'
    def visit_BitAnd(self, n: ast.BitAnd): return '&'
    def visit_FloorDiv(self, n: ast.FloorDiv): return '/'
    def visit_Invert(self, n: ast.Invert): return '~'
    def visit_Not(self, n: ast.Not): return '!'
    def visit_UAdd(self, n: ast.UAdd): return '+'
    def visit_USub(self, n: ast.USub): return '-'
    def visit_Eq(self, n: ast.Eq): return '=='
    def visit_NotEq(self, n: ast.NotEq): return '!='
    def visit_Lt(self, n: ast.Lt): return '<'
    def visit_LtE(self, n: ast.LtE): return '<='
    def visit_Gt(self, n: ast.Gt): return '>'
    def visit_GtE(self, n: ast.GtE): return '>='
    def visit_Is(self, n: ast.Is):  assert False
    def visit_IsNot(self, n: ast.IsNot):  assert False
    def visit_In(self, n: ast.In):  assert False
    def visit_NotIn(self, n: ast.NotIn):  assert False


def parse_annotation(ann: ast.Expression) -> tt.Tuple[tt.Sequence[str], str]:
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
            res = translate(defn)
            print(res)
            from prettyprint import Printer
            print(Printer().visit(res))
            from sessionfer import infer_stype
            print(infer_stype(res))


if __name__ == '__main__':
    with open('examples.py') as f:
        parse_examples(f.read())
