import ast
from ast import NodeVisitor, Expr

from nodes import *
import typing as tt
from solidifier import to_str


class StraightLineVisitor(NodeVisitor):
    """Visitor for handling a block with
    * assignment
    * declaration
    * await statement
    * expression statement
    """

    statements: tt.List[tt.Any] = None
    # types of simple variables
    decls: SymbolTable = None
    # types of class variables
    role_of: RoleTable = None

    def __init__(self, role_of: SymbolTable):
        self.statements = []
        self.role_of = role_of
        self.decls = {}

    def visit_Assign(self, n: ast.Assign):
        assert len(n.targets) == 1
        target = n.targets[0]
        if isinstance(n.value, ast.Await):
            expr = n.value.value
            if isinstance(target, ast.Tuple):
                targets = target.elts
                rvals = expr.elts
                if len(rvals) != len(targets):
                    raise SyntaxWarning
                self.handle_parallel_join(list(zip(targets, rvals)))
            elif isinstance(expr, ast.Name):
                join = self.handle_join(target, expr)
                self.statements.append(join)
            else:
                assert False
        else:
            self.decls[target.id] = 'unknown'
            self.statements.append(to_str(n))

    def handle_await(self, role: str, var_name: str) -> WaitItem:
        var = VarDecl(var_name, self.type_of(role, var_name))
        return WaitItem(role, var, [])

    def type_of(self, role: str, attr: str):
        return self.role_of[role].future_items[attr]

    def add_decls(self, name: str, role: RoleClass):
        self.decls[name] = 'address'
        for d in [role.init_items, role.future_items, role.money_items]:
            for attr, type in d.items():
                self.decls[mangle(name, attr)] = type

    def handle_join(self, target: ast.Name, expr: tt.Union[ast.Expr, ast.Name]) -> JoinItem:
        tag, role_name = get_tag_and_name(expr)
        role = self.role_of[role_name]
        self.role_of[target.id] = role
        self.add_decls(target.id, role)
        return JoinItem(to_str(target), tag, role)

    def handle_parallel_join(self, items: tt.Sequence[tt.Tuple[ast.Name, Expr]]):
        joins = Parallel([self.handle_join(target, expr) for target, expr in items])
        self.statements.append(joins)

    def handle_parallel_await(self, items: tt.Sequence[ast.Attribute]):
        waits = Parallel([self.handle_await(name, attr) for name, attr in items])
        self.statements.append(waits)

    def visit_Await(self, value):
        assert False

    def visit_Yield(self, value):
        pass

    def visit_YieldFrom(self, value): pass

    def visit_AugAssign(self, n: ast.AugAssign):
        self.statements.append(to_str(n))

    def visit_AnnAssign(self, s: ast.AnnAssign):
        t = to_str(s.annotation)
        if t in self.role_of:
            t = 'address'
        self.decls[s.target.id] = t
        if s.value:
            self.statements.append(f'{s.target.id} = {to_str(s.value)}')

    def visit_ClassDef(self, name, bases, keywords, body, decorator_list): pass

    def visit_FunctionDef(self, name, args, body, decorator_list, returns): pass

    def visit_AsyncFunctionDef(self, d: ast.AsyncFunctionDef):
        self.iter_block(d.body)

    def iter_block(self, block: tt.List[ast.AST]):
        for stmt in block:
            self.visit(stmt)

    def visit_Expr(self, body: Expr):
        expr = body.value
        if isinstance(expr, ast.Call):
            call = expr
            if to_str(call.func) == 'declare':
                assert len(call.args) == 1
                self.statements.append(Declare(to_str(call.args[0])))
            if to_str(call.func) == 'pay':
                assert len(call.args) >= 2
                to, *args = call.args
                self.statements.append(Pay(to_str(to), [to_str(arg) for arg in args]))
        elif isinstance(expr, ast.Await):
            attr = expr.value
            assert isinstance(attr, ast.Attribute)
            assert isinstance(attr.value, ast.Name)
            wait = self.handle_await(attr.value.id, attr.attr)
            self.statements.append(wait)

    def visit_For(self, target, iter, body, orelse): pass

    def visit_AsyncFor(self, target, iter, body, orelse): pass

    def visit_While(self, test, body, orelse): pass

    def visit_Break(self): pass

    def visit_Continue(self): pass

    def visit_With(self, items, body): pass

    def visit_AsyncWith(self, items, body): pass

    def visit_ClassDef(self, n: ast.ClassDef):
        # do nothing
        pass


def get_tag_and_name(expr: ast.Expr):
    if isinstance(expr, ast.Name):
        return expr.id, expr.id
    elif isinstance(expr, ast.Call):
        assert isinstance(expr.func, ast.Name)
        [tag] = expr.args
        return tag.s, expr.func.id


def find_roles(node):
    roles: tt.Dict[str, RoleClass] = {}
    for cls in ast.walk(node):
        if isinstance(cls, ast.ClassDef):
            decl = RoleCreator()
            decl.generic_visit(cls)
            roles[cls.name] = decl.to_role(cls.name)
    return roles


class RoleCreator(NodeVisitor):
    decls: SymbolTable = None
    requires = None
    futures: SymbolTable = None
    moneys: SymbolTable = None

    def __init__(self):
        self.decls = {}
        self.requires = []
        self.futures = {}
        self.moneys = {}

    def visit_AnnAssign(self, st: ast.AnnAssign):
        annotation = st.annotation
        sym = self.decls
        if isinstance(annotation, ast.Subscript):
            assert st.annotation.value.id == 'future'
            annotation = annotation.slice.value
            sym = self.futures
        elif to_str(annotation) == 'money':
            sym = self.moneys
        sym[to_str(st.target)] = to_str(annotation)

    def visit_Call(self, call: ast.Call):
        if to_str(call.func) == 'require':
            assert len(call.args) == 1
            self.requires.append(to_str(call.args[0]))

    def to_role(self, name: str):
        return RoleClass(name, self.decls, self.requires, self.futures, self.moneys)

    def visit_ClassDef(self, n: ast.ClassDef):
        # do nothing
        pass


def make_model(defn: ast.AsyncFunctionDef):
    role_of = find_roles(defn)
    slv = StraightLineVisitor(role_of)
    slv.visit(defn)
    return slv.decls, slv.statements
