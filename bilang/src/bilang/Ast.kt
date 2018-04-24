package bilang

sealed class Ast

data class ExpProgram(val desc: String, val types: Map<String, TypeExp>, val game: Ext) : Ast()

interface Step

sealed class Ext : Ast() {
    data class Bind(val kind: Kind, val qs: List<Query>, val ext: Ext) : Ext(), Step
    data class BindSingle(val kind: Kind, val q: Query, val ext: Ext) : Ext(), Step
    data class Value(val exp: Payoff.Value) : Ext()
}
data class Query(val role: Exp.Var, val params: List<VarDec>, val deposit: Exp.Const.Num, val where: Exp) : Ast()

sealed class Exp : Ast() {
    data class Call(val target: Var, val args: List<Exp>) : Exp()
    data class UnOp(val op: String, val operand: Exp) : Exp()
    data class BinOp(val op: String, val left: Exp, val right: Exp) : Exp()

    data class Var(val name: String) : Exp()
    data class Member(val target: String, val field: String) : Exp()
    data class Cond(val cond: Exp, val ifTrue: Exp, val ifFalse: Exp) : Exp()

    sealed class Const : Exp() {
        object UNDEFINED : Const()
        data class Num(val n: Int) : Const()
        data class Bool(val truth: Boolean) : Const()
        data class Address(val n: Int) : Const()
        data class Hidden(val value: Const) : Const()
    }
    data class Let(val dec: VarDec, val init: Exp, val exp: Exp) : Exp()
}

sealed class Payoff: Ast() {
    data class Cond(val cond: Exp, val ifTrue: Payoff, val ifFalse: Payoff) : Payoff()
    // Idea: not a simple Var -> Exp mapping, but a `lambda (Var : RoleSet) . Exp` mapping
    // (the trivial case where RoleSet is a singleton van have Var -> Exp as a syntactic sugar)
    // This sounds like dependent types, but no complex type checking is involved.

    data class Value(val ts: Map<String, Exp>) : Payoff()
    data class Let(val dec: VarDec, val init: Exp, val payoff: Payoff) : Payoff()
}

data class VarDec(val name: Exp.Var, val type: TypeExp) : Ast()
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
    data class Subset(val values: Set<Exp.Const.Num>) : TypeExp(), IntClass
    data class Range(val min: Exp.Const.Num, val max: Exp.Const.Num) : TypeExp(), IntClass
    data class Opt(val type: TypeExp) : TypeExp()
}

internal fun findRoles(ext: Ext): List<String> = when (ext) {
    is Ext.Bind -> (if (ext.kind == Kind.JOIN) ext.qs.map { it.role.name } else listOf()) + findRoles(ext.ext)
    is Ext.BindSingle -> (if (ext.kind == Kind.JOIN) listOf(ext.q.role.name) else listOf()) + findRoles(ext.ext)
    is Ext.Value -> listOf()
}

fun desugar(payoff: Payoff): Payoff.Value = desugar(payoff, listOf())

// TODO: FIX. let binding does not seem to happen
private fun desugar(payoff: Payoff, names: List<Pair<VarDec, Exp>>): Payoff.Value = when (payoff) {
    is Payoff.Value -> payoff.copy(ts = payoff.ts.mapValues { (_, exp) ->
        names.foldRight(exp){(vd, init), acc -> Exp.Let(vd, init, acc)}
    })
    is Payoff.Cond -> {
        val ifTrue = desugar(payoff.ifTrue).ts
        val ifFalse = desugar(payoff.ifFalse).ts
        val ts = ifTrue.keys.map { Pair(it, Exp.Cond(payoff.cond, ifTrue.getValue(it), ifFalse.getValue(it))) }.toMap()
        Payoff.Value(ts)
    }
    is Payoff.Let -> desugar(payoff.payoff, names + Pair(payoff.dec, payoff.init))
}

