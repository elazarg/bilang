package bilang

sealed class Ast

data class Program(val typedecls: List<TypeDec>, val block: Block) : Ast()

data class Block(val stmts: List<Stmt>): Ast()
data class TypeDec(val name: String, val definition: TypeExp) : Ast()

sealed class TypeExp : Ast() {
    object INT: TypeExp()
    object BOOL: TypeExp()
    object ROLE: TypeExp()
    data class TypeId(val name: String): TypeExp()
    data class Subset(val values: Set<Exp.Num>): TypeExp()
    data class Range(val min: Exp.Num, val max: Exp.Num): TypeExp()
}

sealed class Exp : Ast() {
    data class Call(val target: Var, val args: List<Exp>) : Exp()
    data class UnOp(val op: String, val operand: Exp) : Exp()
    data class BinOp(val op: String, val left: Exp, val right: Exp) : Exp()
    data class Num(val n: Int) : Exp()
    data class Address(val n: Int) : Exp()
    data class Var(val name: String) : Exp()
    data class Member(val target: Var, val field: String) : Exp()
    data class Cond(val cond: Exp, val ifTrue: Exp, val ifFalse: Exp) : Exp()
    object UNDEFINED : Exp()
}

sealed class Stmt : Ast() {
    sealed class Def: Stmt() {
        data class VarDef(val dec: VarDec, val init: Exp) : Def()
        data class YieldDef(val packets: Packets, val hidden: Boolean) : Def()
        data class JoinDef(val packets: Packets, val hidden: Boolean) : Def()
        data class JoinManyDef(val role: String) : Def()
    }

    data class Assign(val target: String , val exp: Exp): Stmt()
    data class Reveal(val target: String, val where: Exp): Stmt()
    data class If(val cond: Exp, val ifTrue: Block, val ifFalse: Block): Stmt()
    data class ForYield(val from: String, val packets: Packets, val block: Block): Stmt()
    data class Transfer(val amount: Exp, val from: Exp, val to: Exp): Stmt()
}

data class VarDec(val name: String, val type: TypeExp) : Ast()
data class Packet(val role: String, val params: List<VarDec>) : Ast()
data class Packets(val packets: List<Packet>, val where: Exp) : Ast()
