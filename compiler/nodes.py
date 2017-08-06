from typing import NamedTuple
import typing as tt

SymbolTable = tt.Dict[str, str]


class VarDecl(NamedTuple):
    name: str
    type: str


class RoleClass(NamedTuple):
    role_name: str
    init_items: SymbolTable
    requires: tt.List[str]
    future_items: SymbolTable
    money_items: SymbolTable


RoleTable = tt.Dict[str, RoleClass]


class JoinItem(NamedTuple):
    var_name: str
    tag: str
    role_class: RoleClass


class WaitItem(NamedTuple):
    role: str
    var: VarDecl
    requires: tt.List[str]


class Parallel(NamedTuple):
    items: tt.List[tt.Union[JoinItem, WaitItem]]


class Declare(NamedTuple):
    declaration: str


class Pay(NamedTuple):
    to: str
    amounts: tt.List[str]


def mangle(name: str, attr: str) -> str:
    return f'{name}__{attr}'
