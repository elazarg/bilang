package bilang

import bilang.Exp.*
import bilang.Exp.Const.*

fun smt(g: ExpProgram) = ext(g.game)

private fun ext(e: Ext): String = when (e) {
    is Ext.Bind -> TODO()
    is Ext.BindSingle -> {
        val vars = e.q.params.map { (name, type) -> Pair(Member(e.q.role, name), type) }
        val decls = vars.map { (m, type) -> "(declare-const ${exp(m)} ${smtTypeOf(type)})" }.join("\n")
        val dones = vars.map { (m, _) -> "(declare-const ${exp(m)}_done Bool)" }.join("\n")
        val where = exp(e.q.where)
        """
        |$decls
        |$dones
        |
        |(assert $where)
        |
        |${ext(e.ext)}
        """.trimMargin()
    }
    is Ext.Value -> {
        e.exp.ts.map { (a, b) ->
            "(assert ${exp(BinOp("=", Member(a, "outcome"), b))})"
        }.join("\n")
    }
}


private fun exp(e: Exp): String = when (e) {
    is Call -> TODO()
    is UnOp -> if (e.op == "isUndefined") {
        val operand = e.operand as Member
        "(not ${operand.target}_${operand.field}_done)"
    } else "(${e.op} ${exp(e.operand)})"
    is BinOp -> {
        val op = when (e.op) {
            "<->" -> "iff"
            "<-!->" -> "!="
            "==" -> "="
            "!=" -> "<>"
            "&&" -> "and"
            "||" -> "or"
            else -> e.op
        }
        "($op ${exp(e.left)} ${exp(e.right)})"
    }
    is Var -> e.name
    is Member -> "${e.target}_${e.field}"
    is Cond -> "(ite ${exp(e.cond)} ${exp(e.ifTrue)} ${exp(e.ifFalse)})"
    is Num -> "${e.n}"
    is Bool -> "${e.truth}"
    is Address -> TODO()
    is Hidden -> exp(e.value as Exp)
    is Let -> TODO()
    UNDEFINED -> throw StaticError("Undefined")
}


private fun smtTypeOf(t: TypeExp): String = when (t) {
    TypeExp.INT -> "Int"
    TypeExp.BOOL -> "Bool"
    TypeExp.ROLE -> TODO()
    TypeExp.ROLESET -> TODO()
    TypeExp.ADDRESS -> "Int"
    TypeExp.EMPTY -> throw AssertionError()
    is TypeExp.Hidden -> smtTypeOf(t.type)
    is TypeExp.TypeId -> t.name
    is TypeExp.Subset -> "Int"
    is TypeExp.Range -> "Int"
    is TypeExp.Opt -> TODO()
}


fun main(args: Array<String>) {
    val e = BinOp("<", Num(5), Member("Host", "choice"))
    println(e)
    println(exp(e))
}

