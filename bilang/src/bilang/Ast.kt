package bilang

sealed class Ast

data class Program(val typedecls: List<TypeDec>, val block: Stmt.Block) : Ast()

data class ExpProgram(val name: String, val desc: String, val typedecls: List<TypeDec>, val game: Exp.Ext) : Ast()


sealed class Exp : Ast() {
    data class Call(val target: Var, val args: List<Exp>) : Exp()
    data class UnOp(val op: String, val operand: Exp) : Exp()
    data class BinOp(val op: String, val left: Exp, val right: Exp) : Exp()

    data class Var(val name: String) : Exp()
    data class Member(val target: Var, val field: String) : Exp()
    data class Cond(val cond: Exp, val ifTrue: Exp, val ifFalse: Exp) : Exp()

    interface Step
    interface Const : Step
    object UNDEFINED : Exp(), Const
    data class Num(val n: Int) : Exp(), Const
    data class Bool(val truth: Boolean) : Exp(), Const
    data class Address(val n: Int) : Exp(), Const
    data class Hidden(val value: Const) : Exp(), Const


    sealed class Ext : Exp(), Step {
        data class Yield(val p: Packet, val exp: Exp, val hidden: Boolean = false) : Ext()
        data class Join(val p: Packet, val exp: Exp, val hidden: Boolean = false) : Ext()
        data class Reveal(val v: Member, val exp: Exp) : Ext() // TODO: where
        data class Parallel<out T : Ext>(val qs: List<T>) : Ext() {
            constructor(vararg qs: T) : this(qs.toList())
        }
    }

    // Not in concrete syntax:
    sealed class Q : Exp() {
        data class Let(val dec: VarDec, val value: Exp) : Q()
        // Var is not evaluated, since the analysis does not handle addresses but roles.
        // giving different payoff for different addresses of the same roles is a TODO

        // Idea: not a simple Var -> Exp mapping, but a `lambda (Var : RoleSet) . Exp` mapping
        // (the trivial case where RoleSet is a singleton van have Var -> Exp as a syntactic sugar)
        // This sounds like dependent types, but no complex type checking is involved.

        // Note that `Exp` here is too much. It should be "SimpleExp".
        data class Payoff(val ts: Map<Var, Exp>) : Q()
        // Payoff is considered constant only when all the Exp are Num.
        // `Num` should be replaced by a tuple of monetary values, parameterized
        data class PayoffConst(val ts: Map<Var, Num>) : Q(), Const
    }
}

sealed class Stmt : Ast() {
    interface External

    data class Block(val stmts: List<Stmt>): Stmt()
    data class Assign(val target: Exp.Var , val exp: Exp): Stmt()
    data class Reveal(val target: Exp.Var, val where: Exp): Stmt(), External
    data class If(val cond: Exp, val ifTrue: Stmt, val ifFalse: Stmt): Stmt()
    data class ForYield(val from: Exp.Var, val packet: Packet, val stmt: Stmt): Stmt()
    data class Transfer(val amount: Exp, val from: Exp, val to: Exp): Stmt()

    data class VarDef(val dec: VarDec, val init: Exp) : Stmt()

    data class JoinManyDef(val role: Exp.Var) : Stmt(), External
    data class JoinDef(val packets: List<Packet>, val hidden: Boolean) : Stmt(), External
    data class YieldDef(val packets: List<Packet>, val hidden: Boolean) : Stmt(), External
}

data class VarDec(val name: Exp.Var, val type: TypeExp) : Ast()
data class Packet(val role: Exp.Var, val params: List<VarDec> = listOf(), val where: Exp = Exp.Bool(true)) : Ast()
enum class GameAction { JOIN, YIELD }

data class TypeDec(val name: String, val definition: TypeExp) : Ast()

sealed class TypeExp : Ast() {
    object INT: TypeExp(), IntClass
    object BOOL: TypeExp()
    object ROLE: TypeExp()
    object ROLESET: TypeExp()
    object ADDRESS: TypeExp()
    object UNIT: TypeExp()
    data class Hidden(val type: TypeExp): TypeExp()
    data class TypeId(val name: String): TypeExp()
    interface IntClass
    data class Subset(val values: Set<Exp.Num>): TypeExp(), IntClass
    data class Range(val min: Exp.Num, val max: Exp.Num): TypeExp(), IntClass
}
