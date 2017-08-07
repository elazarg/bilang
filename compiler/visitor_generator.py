import nodes

cls_fmt = '''\
from typing import TypeVar, Generic, Sequence, Union, Any
from {mod} import Exp, Lvalue, {exports}

_T = TypeVar('_T')
_Q = TypeVar('_Q')


class Visitor(Generic[_T, _Q]):
    def visit(self, node) -> _T:
        return getattr(self, 'visit_' + type(node).__name__)(node)


class ExpVisitor(Generic[_T], Visitor[Exp, _T]):
    {exp_defs}

class LvalVisitor(Generic[_T], Visitor[Lvalue, _T]):
    {lval_defs}

class StmtVisitor(Generic[_T], Visitor[Any, _T]):
    {stmt_defs}

class NodeVisitor(Generic[_T], ExpVisitor[_T], StmtVisitor[_T], LvalVisitor[_T]):
    pass
'''

def_fmt = '''
    def visit_{name}(self, node: {name}) -> _T:
        raise NotImplementedError
'''


def pretty(ann, exports, *, slabolg={id(v): u for u, v in vars(nodes).items()}):
    if hasattr(ann, '__args__'):
        args = ann.__args__
        k = slabolg.get(id(ann))
        if k is not None:
            exports.add(k)
            return k
        if len(args) > 1:
            return f'Union[{", ".join(pretty(arg, exports) for arg in args)}]'
        return f'Sequence[{pretty(args[0], exports)}]'
    if hasattr(ann, '__name__'):
        return ann.__name__
    if hasattr(ann, '__forward_arg__'):
        return ann.__forward_arg__


def generate_visitor():
    vs = vars(nodes)
    mod = 'nodes'
    exports = set()
    exp_names = {pretty(arg, exports) for arg in nodes.Exp.__args__}
    lval_names = {pretty(arg, exports) for arg in nodes.Lvalue.__args__}
    stmt_defs = []
    exp_defs = []
    lval_defs = []
    for name, v in vs.items():
        if hasattr(v, '_field_types'):
            exports.add(name)
            method = def_fmt.format(name=name)
            if name in exp_names:
                exp_defs.append(method)
            elif name in lval_names:
                lval_defs.append(method)
            else:
                stmt_defs.append(method)
    return cls_fmt.format(stmt_defs=''.join(stmt_defs),
                          exp_defs=''.join(exp_defs),
                          lval_defs=''.join(lval_defs),
                          exports=', '.join(exports),
                          mod=mod)

if __name__ == '__main__':
    with open('generated/visitor.py', 'w') as f:
        print(generate_visitor(), file=f, end='')
