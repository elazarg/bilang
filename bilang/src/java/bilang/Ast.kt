package bilang

sealed class Ast

data class Program(val typedecls: List<TypeDec>, val block: Stmt.Block) : Ast()

data class TypeDec(val name: String, val definition: TypeExp) : Ast()

sealed class TypeExp : Ast() {
    object INT: TypeExp(), IntClass
    object BOOL: TypeExp()
    object ROLE: TypeExp()
    object ROLESET: TypeExp()
    object ADDRESS: TypeExp()
    object UNIT: TypeExp()
    data class TypeId(val name: String): TypeExp()
    interface IntClass
    data class Subset(val values: Set<Exp.Num>): TypeExp(), IntClass
    data class Range(val min: Exp.Num, val max: Exp.Num): TypeExp(), IntClass
}

sealed class Exp : Ast() {
    data class Call(val target: Var, val args: List<Exp>) : Exp()
    data class UnOp(val op: String, val operand: Exp) : Exp()
    data class BinOp(val op: String, val left: Exp, val right: Exp) : Exp()

    data class Var(val name: String) : Exp()
    data class Member(val target: Var, val field: String) : Exp()
    data class Cond(val cond: Exp, val ifTrue: Exp, val ifFalse: Exp) : Exp()

    interface Const
    object UNDEFINED : Exp(), Const
    data class Num(val n: Int) : Exp(), Const
    data class Address(val n: Int) : Exp(), Const

    // Not in concrete syntax:
    sealed class Q : Exp() {
        data class Y(val p: Packet, val exp: Exp, val hidden: Boolean = false) : Q()
        data class Let(val dec: VarDec, val value: Exp) : Q()
        data class Transfers(val ts: List<Stmt.Transfer>) : Q()
    }
}

sealed class Stmt : Ast() {
    interface External

    sealed class Def: Stmt() {
        data class VarDef(val dec: VarDec, val init: Exp) : Def()
        data class YieldDef(val packets: List<Packet>, val hidden: Boolean) : Def(), External
        data class JoinDef(val packets: List<Packet>, val hidden: Boolean) : Def(), External
        data class JoinManyDef(val role: Exp.Var) : Def(), External
    }

    data class Block(val stmts: List<Stmt>): Stmt()
    data class Assign(val target: Exp.Var , val exp: Exp): Stmt()
    data class Reveal(val target: Exp.Var, val where: Exp): Stmt(), External
    data class If(val cond: Exp, val ifTrue: Block, val ifFalse: Block): Stmt()
    data class ForYield(val from: Exp.Var, val packet: Packet, val block: Block): Stmt()
    data class Transfer(val amount: Exp, val from: Exp.Var, val to: Exp.Var): Stmt()
}

data class VarDec(val name: Exp.Var, val type: TypeExp) : Ast()
data class Packet(val role: Exp.Var, val params: List<VarDec>, val where: Exp) : Ast()
