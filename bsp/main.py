from typing import *

Agent = int
RoleVarname = str
Commitment = int
Typename = str
Value = object
Varname = str
Exp = str
FoldExp = Exp
WhereExp = Exp


class JoinStep:
    joins: Dict[RoleVarname, Agent]


class BigStepProg:
    action: Dict[RoleVarname, Tuple[Action, Varname, WhereExp, FoldExp]]
    timeout: int  # easier to assume that's the only progress, and it is global to the step
    commands: List[Tuple[Varname, Exp]]
