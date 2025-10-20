package vegas

sealed class Ast

interface Step

data class Role(val name: String) : Ast() {
    override fun toString(): String = name
}

sealed class Ext : Ast() {
    data class Bind(val kind: Kind, val qs: List<Query>, val ext: Ext) : Ext(), Step
    data class BindSingle(val kind: Kind, val q: Query, val ext: Ext) : Ext(), Step
    data class Value(val outcome: Outcome) : Ext()
}

data class Query(val role: Role, val params: List<VarDec>, val deposit: Exp.Const.Num, val where: Exp) : Ast()

sealed class Exp : Ast() {
    data class Call(val target: Var, val args: List<Exp>) : Exp()
    data class UnOp(val op: String, val operand: Exp) : Exp()
    data class BinOp(val op: String, val left: Exp, val right: Exp) : Exp()

    data class Var(val name: String) : Exp() {
        override fun toString(): String = name
    }

    data class Member(val target: Role, val field: Var) : Exp()
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

sealed class Outcome : Ast() {
    data class Cond(val cond: Exp, val ifTrue: Outcome, val ifFalse: Outcome) : Outcome()
    // Idea: not a simple Var -> Exp mapping, but a `lambda (Var : RoleSet) . Exp` mapping
    // (the trivial case where RoleSet is a singleton van have Var -> Exp as a syntactic sugar)
    // This sounds like dependent types, but no complex type checking is involved.

    data class Value(val ts: Map<Role, Exp>) : Outcome()
    data class Let(val dec: VarDec, val init: Exp, val outcome: Outcome) : Outcome()
}

data class VarDec(val v: Exp.Var, val type: TypeExp)

enum class Kind { JOIN, YIELD, REVEAL, JOIN_CHANCE }

sealed class TypeExp : Ast() {
    object INT : TypeExp(), IntClass
    object BOOL : TypeExp()
    object ADDRESS : TypeExp()
    object EMPTY : TypeExp()

    data class Hidden(val type: TypeExp) : TypeExp()
    data class TypeId(val name: String) : TypeExp() {
        override fun toString(): String = name
    }

    interface IntClass
    data class Subset(val values: Set<Exp.Const.Num>) : TypeExp(), IntClass
    data class Range(val min: Exp.Const.Num, val max: Exp.Const.Num) : TypeExp(), IntClass
    data class Opt(val type: TypeExp) : TypeExp()
}

data class ExpProgram(val name: String, val desc: String, val types: Map<TypeExp.TypeId, TypeExp>, val game: Ext) :
    Ast()


internal fun findRolesWithChance(ext: Ext): List<Role> = when (ext) {
    is Ext.Bind -> (if (ext.kind == Kind.JOIN || ext.kind == Kind.JOIN_CHANCE) ext.qs.map { it.role } else setOf()) + findRoles(
        ext.ext
    )

    is Ext.BindSingle -> (if (ext.kind == Kind.JOIN || ext.kind == Kind.JOIN_CHANCE) listOf(ext.q.role) else setOf()) + findRoles(
        ext.ext
    )

    is Ext.Value -> listOf()
}

internal fun findRoles(ext: Ext): List<Role> = when (ext) {
    is Ext.Bind -> (if (ext.kind == Kind.JOIN) ext.qs.map { it.role } else setOf()) + findRoles(ext.ext)
    is Ext.BindSingle -> (if (ext.kind == Kind.JOIN) listOf(ext.q.role) else setOf()) + findRoles(ext.ext)
    is Ext.Value -> listOf()
}

fun desugar(outcome: Outcome): Outcome.Value = desugar(outcome, listOf())

private fun <T : Ast> copySpan(to: T, from: Ast): T {
    SourceLoc.copy(to, from)
    return to
}

// TODO: FIX. let binding does not seem to happen
private fun desugar(outcome: Outcome, names: List<Pair<VarDec, Exp>>): Outcome.Value = when (outcome) {
    is Outcome.Value -> outcome.copy(ts = outcome.ts.mapValues { (_, exp) ->
        names.foldRight(exp) { (vd, init), acc -> copySpan(Exp.Let(vd, init, acc), outcome) }
    })

    is Outcome.Cond -> {
        val ifTrue = desugar(outcome.ifTrue).ts
        val ifFalse = desugar(outcome.ifFalse).ts
        fun safeGetRole(m: Map<Role, Exp>, role: Role): Exp {
            try {
                return m.getValue(role)
            } catch (e: NoSuchElementException) {
                throw StaticError("$role is not a role", role)
            }
        }

        val ts = ifTrue.keys.associateWith {
            copySpan(Exp.Cond(outcome.cond, safeGetRole(ifTrue, it), safeGetRole(ifFalse, it)), it)
        }
        copySpan(Outcome.Value(ts), outcome)
    }

    is Outcome.Let -> desugar(outcome.outcome, names + Pair(outcome.dec, outcome.init))
}

