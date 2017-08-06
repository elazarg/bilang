import ast
from ast import NodeVisitor


class SolidityPrinter(NodeVisitor):
    def visit_Module(self, node: ast.Module):
        return '\n'.join(self.visit(stmt) for stmt in node.body)

    def visit_Await(self, value): pass

    def visit_Yield(self, value): pass

    def visit_YieldFrom(self, value): pass

    def visit_Assign(self, n: ast.Assign):
        # target, annotation, value, simple
        #ann = self.visit(s.annotation)
        #var = self.visit(s.target)
        #value = ' = ' + self.visit(s.value) if s.value is not None else ''
        return f'{to_str(n.targets[0])} = {to_str(n.value)}'

    def visit_AugAssign(self, target, op, value): pass

    def visit_AnnAssign(self, s: ast.AnnAssign):
        # target, annotation, value, simple
        ann = self.visit(s.annotation)
        var = self.visit(s.target)
        value = ' = ' + self.visit(s.value) if s.value is not None else ''
        return f'{ann} {var}{value}'

    def visit_If(self, n: ast.If): pass

    def visit_ClassDef(self, n: ast.ClassDef):
        # do nothing
        pass

    def visit_FunctionDef(self, name, args, body, decorator_list, returns): pass

    def visit_AsyncFunctionDef(self, name, args, body, decorator_list, returns): pass

    def visit_For(self, target, iter, body, orelse): pass

    def visit_AsyncFor(self, target, iter, body, orelse): pass

    def visit_With(self, items, body): pass

    def visit_AsyncWith(self, items, body): pass

    def visit_While(self, test, body, orelse): pass

    def visit_Break(self): return 'break'

    def visit_Continue(self): return 'continue'

    def visit_Attribute(self, n: ast.Attribute):
        return f'{self.visit(n.value)}__{n.attr}'

    def visit_Name(self, node: ast.Name):
        return node.id

    def visit_Num(self, node: ast.Num):
        return str(node.n)

    def visit_Str(self, node: ast.Str):
        return repr(node.s)

    def visit_NameConstant(self, node: ast.NameConstant):
        return str(node)

    def visit_Expr(self, body: ast.Expr):
        return self.visit(body.value)

    def visit_List(self, n: ast.List): assert False

    def visit_Tuple(self, elts, ctx): pass

    def visit_BoolOp(self, n: ast.BoolOp):
        s = ' ' + self.visit(n.op) + ' '
        return f'({s.join(self.visit(x) for x in n.values)})'

    def visit_Compare(self, n: ast.Compare):
        assert len(n.comparators) == 1
        return f'{self.visit(n.left)} {self.visit(n.ops[0])} {self.visit(n.comparators[0])}'

    def visit_BinOp(self, n: ast.BinOp):
        return f'({self.visit(n.left)} {self.visit(n.op)} {self.visit(n.right)})'

    def visit_UnaryOp(self, n):
        return f'({self.visit(n.op)}{self.visit(n.operand)})'

    def visit_Call(self, node: ast.Call):
        sf = self.visit(node.func)
        sargs = [self.visit(a) for a in node.args]
        skw = [self.visit(k) for k in node.keywords]
        both = ', '.join(sargs + skw)
        return f'{sf}({both})'

    def visit_IfExp(self, n: ast.IfExp):
        return f'({self.visit(n.test)} ? {self.visit(n.body)} : {self.visit(n.orelse)})'

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


p = SolidityPrinter()


def to_str(node):
    return p.visit(node)
