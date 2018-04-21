package bilang

sealed class Ast

data class ExpProgram(val desc: String, val types: Map<String, TypeExp>, val game: Ext) : Ast()

interface Step

sealed class Ext : Ast() {
    data class Bind(val qs: List<Query>, val ext: Ext) : Ext(), Step
    data class BindSingle(val q: Query, val ext: Ext) : Ext(), Step
    data class Value(val exp: Exp) : Ext()
}

sealed class Exp : Ast() {
    data class Call(val target: Var, val args: List<Exp>) : Exp()
    data class UnOp(val op: String, val operand: Exp) : Exp()
    data class BinOp(val op: String, val left: Exp, val right: Exp) : Exp()

    data class Var(val name: String) : Exp()
    data class Member(val target: Var, val field: String) : Exp()
    data class Cond(val cond: Exp, val ifTrue: Exp, val ifFalse: Exp) : Exp()

    interface Const : Step
    object UNDEFINED : Exp(), Const
    data class Num(val n: Int) : Exp(), Const
    data class Bool(val truth: Boolean) : Exp(), Const
    data class Address(val n: Int) : Exp(), Const
    data class Hidden(val value: Const) : Exp(), Const

    data class Let(val dec: VarDec, val init: Exp, val exp: Exp) : Exp()

    // Var is not evaluated, since the analysis does not handle addresses but roles.
    // giving different payoff for different addresses of the same roles is a TODO

    // Idea: not a simple Var -> Exp mapping, but a `lambda (Var : RoleSet) . Exp` mapping
    // (the trivial case where RoleSet is a singleton van have Var -> Exp as a syntactic sugar)
    // This sounds like dependent types, but no complex type checking is involved.

    // Note that `Exp` here is too much. It should be "SimpleExp".
    data class Payoff(val ts: Map<Var, Exp>) : Exp(), Const

    // Payoff is considered constant only when all the Exp are Num.
    // `Num` should be replaced by a tuple of monetary values, parameterized
    //data class PayoffConst(val ts: Map<Var, Num>) : Exp(), Const
}

data class VarDec(val name: Exp.Var, val type: TypeExp) : Ast()
data class Query(val kind: Kind, val role: Exp.Var, val params: List<VarDec> = listOf(), val where: Exp = Exp.Bool(true)) : Ast()
enum class Kind { JOIN, YIELD, REVEAL, MANY }

sealed class TypeExp : Ast() {
    object INT : TypeExp(), IntClass
    object BOOL : TypeExp()
    object ROLE : TypeExp()
    object ROLESET : TypeExp()
    object ADDRESS : TypeExp()
    data class Hidden(val type: TypeExp) : TypeExp()
    data class TypeId(val name: String) : TypeExp()
    interface IntClass
    data class Subset(val values: Set<Exp.Num>) : TypeExp(), IntClass
    data class Range(val min: Exp.Num, val max: Exp.Num) : TypeExp(), IntClass
    data class Opt(val type: TypeExp) : TypeExp()
}

fun hide(type: TypeExp) = type as? TypeExp.Hidden ?: TypeExp.Hidden(type)

fun independent(qs: List<Query>, exp: Ext): Ext.Bind {
    val reveal = Ext.Bind(qs.map { it.copy(kind = Kind.REVEAL, params = it.params.filterNot { it.type is TypeExp.Hidden }) }, exp)
    return Ext.Bind(qs.map { it.copy(params = it.params.map { p -> p.copy(type = hide(p.type)) }) },
            if (qs.any { it.params.isNotEmpty() }) reveal else exp)
}

