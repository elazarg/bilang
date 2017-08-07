from typing import *
from infos import *

State = int


STEP_VAR = {'_step_count': 'uint'}


def str_args(vs: Sequence[VarDecl]) -> str:
    return ', '.join(f'{type} {name}' for name, type in vs.items())


def str_inits(role: str, names: Sequence[str]):
    return ''.join(f'{mangle(role, name)} = {name}; ' for name in names)


def str_requires(rs: Sequence[str]):
    return ''.join(f'require({r}); ' for r in rs)


def emit_func(src: int, dst: int, kind: str, tag: str, args: str, var_name: str,
              requires: List[str], inits: str, is_parallel: bool) -> None:
    print(f'''
    function state_{src}_{kind}_{tag}({args}) {{''', end='')
    print(f'''
        require(_step_count == step_count);
        require(state == {src});
        if ({var_name} != 0x0) revert();
        {inits}
        {str_requires(requires)}''',
          end='')
    if is_parallel:
        print(f'''
        move_{src}_{dst}_if_done();''', end='')
    else:
        print(f'''
        _step_count += 1;
        state = {dst};''', end='')
    print(f'''
    }}''')


def emit_join(src: State, dst: State, j: JoinItem, is_parallel: bool = False) -> None:
    r = j.role_class
    args = str_args({**r.init_items, **STEP_VAR})
    inits = str_inits(j.var_name, r.init_items)
    inits += f'''
        {j.var_name} = msg.sender;'''
    assert len(r.money_items) <= 1
    requires = r.requires
    for m in r.money_items:
        mn = mangle(j.var_name, m)
        for i, req in enumerate(r.requires):
            if f'{m} == ' in req:
                inits += f'''
        {mn} = {req[len(m) + 4:]};'''
                del requires[i]
            if f'{mn} == ' in req:
                inits += f'''
            {mn} = {req[len(mn) + 4:]};'''
                del requires[i]
    mrs = ' + '.join(mangle(j.var_name, m) for m in r.money_items)
    if mrs:
        inits += f'''
        require({mrs} == msg.value);'''
    emit_func(src, dst, 'join', j.tag, args, j.var_name, requires, inits, is_parallel)


def emit_attr(src: State, dst: State, att: WaitItem, is_parallel: bool = False) -> None:
    args = str_args({att.var_name: att.var_type, **STEP_VAR})
    inits = str_inits(att.role, [att.var_name])
    requires = [f'msg.sender == {att.role}'] + att.requires
    emit_func(src, dst, 'await', att.role, args, att.var_name, requires, inits, is_parallel)


def emit_parallel(src: State, dst: State, p: Parallel) -> None:
    for j in p.items:
        if isinstance(j, JoinItem):
            emit_join(src, dst, j, is_parallel=True)
        if isinstance(j, WaitItem):
            emit_attr(src, dst, j, is_parallel=True)
    parallel_test = ' && '.join(f'{j.var_name} != 0x0' if isinstance(j, JoinItem) else
                                f'{mangle(j.role, j.var_name)}__initialized' if isinstance(j, WaitItem) else '???'
                                for j in p.items)
    print(f'''
    function move_{src}_{dst}_if_done() internal {{
        if ({parallel_test}) {{
            step_count += 1;
            state = {dst};
        }}
    }}''')


def emit_statement(src: State, dst: State, xs: List[str]) -> None:
    lines = ('\n' + ' ' * 8).join(s + ';' for s in xs)
    print(f'''
    function move_{src}_{dst}() {{
        require(state == {src});
        {lines}
        state = {dst};
    }}''')


def emit_end(src: State) -> None:
    print(f'''
    function end() state({src}) {{
        selfdestruct(msg.sender);
    }}
    ''')


def emit_block(items) -> None:
    for src, item in enumerate(items):
        dst = src + 1
        if isinstance(item, JoinItem):
            emit_join(src, dst, item)
        elif isinstance(item, WaitItem):
            emit_attr(src, dst, item)
        elif isinstance(item, Parallel):
            emit_parallel(src, dst, item)
        elif isinstance(item, Declare):
            emit_statement(src, dst, [f'declare({item.declaration})'])
        elif isinstance(item, Pay):
            args = ', '.join(item.amounts)
            emit_statement(src, dst, [f'transfer({item.to}, {args})'])
        elif isinstance(item, str):
            emit_statement(src, dst, [item])
        else:
            assert False, item
    emit_end(dst)


def emit_decls(items: SymbolTable) -> None:
    for name, type in items.items():
        print(f'    {type} {name};')


def print_contract(name: str, decls: SymbolTable, statements):
    print(f'''contract {name} {{
    uint stmt_index = 0;
    uint step_count = 0;
    ''')
    emit_decls(decls)
    emit_block(statements)
    print('}')


if __name__ == '__main__':
    player = RoleClass('A', [VarDecl('choice', 'bool')], [], [])
    emit_parallel(0, 1, Parallel([JoinItem('even', 'Even', player),
                                  JoinItem('odd', 'Odd', player)]))
    emit_parallel(2, 3, Parallel([WaitItem('host', 'goat', 'int', ['goat != guest__door1'])
                                  ]))
    emit_statement(1, 2, ['x = 5', 'y = 2'])

    emit_attr(0, 1, WaitItem('host', 'hidden_car', 'int', []))
    emit_attr(1, 2, WaitItem('guest', 'door1', 'int', []))
    emit_attr(2, 3, WaitItem('host', 'goat', 'int', ['goat != guest__door1']))
    emit_attr(3, 4, WaitItem('guest', 'door2', 'int', ['goat != guest__door2']))
    emit_attr(4, 5, WaitItem('host', 'salt', 'int', []))
    emit_attr(5, 6, WaitItem('host', 'car', 'int', ['sha3(car, salt) == hidden_car', 'goat != car']))
