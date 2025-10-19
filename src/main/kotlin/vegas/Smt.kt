package vegas

import vegas.Exp.*
import vegas.Exp.Const.*

fun smt(g: ExpProgram) = """
    |${defineTypes(g.types)}
    |
    |${ext(g.game)}
    |
    |(check-sat)
    |(get-model)
    """.trimMargin()

private fun defineTypes(types: Map<String, TypeExp>) =
        types.map { (name, _) -> "(define-sort $name () Int)" }.join("\n")

private fun ext(e: Ext): String = when (e) {
    is Ext.Bind -> e.qs.map { bind(it) }.join("\n") + ext(e.ext)
    is Ext.BindSingle -> bind(e.q) + ext(e.ext)
    is Ext.Value -> {
        e.exp.ts.map { (a, b) ->
            val m = Member(a, "outcome")
            // TODO: define-fun? declare-fun?
            "(declare-const ${exp(m)} Int)\n" +
            "(assert ${exp(BinOp("=", m, b))})"
        }.join("\n")
    }
}

private fun bind(q: Query) = if (q.params.isEmpty()) "" else {
    val vars = q.params.filter { it.type !is TypeExp.Hidden }.map { (name, type) -> Pair(Member(q.role, name), type) }
    val decls = vars.map { (m, type) -> "(declare-const ${exp(m)} ${smtTypeOf(type)})" }.join("\n")
    val dones = vars.map { (m, _) -> "(declare-const ${exp(m)}_done Bool)" }.join("\n")
    //val doneQuit = vars.map { (m, _) -> "(assert (=> ${exp(m)}_done last_var_done))" }.join("\n")
    val where = if (q.where != Bool(true)) "(assert ${exp(q.where)})" else ""
    """
    |$decls
    |$dones
    |
    |$where
    |
    """.trimMargin()
}


private fun exp(e: Exp): String = when (e) {
    is Call -> TODO()

    is UnOp -> when (e.op) {
        "isUndefined" -> {
            val m = e.operand as Member
            "(not ${m.target}_${m.field}_done)"
        }
        "isDefined" -> {
            val m = e.operand as Member
            "${m.target}_${m.field}_done"
        }
        else -> "(${unop(e.op)} ${exp(e.operand)})"
    }

    is BinOp ->
        if (e.op == "!=") exp(UnOp("!", e.copy(op = "==")))
        else "(${binop(e.op)} ${exp(e.left)} ${exp(e.right)})"

    is Var -> e.name
    is Member -> "${e.target}_${e.field}"
    is Cond -> "(ite ${exp(e.cond)} ${exp(e.ifTrue)} ${exp(e.ifFalse)})"
    is Num -> "${e.n}"
    is Bool -> "${e.truth}"
    is Address -> TODO()
    is Hidden -> exp(e.value as Exp)
    is Let -> "(let ${e.dec.name} ${exp(e.init)} ${exp(e.exp)})"
    UNDEFINED -> throw StaticError("Undefined")
}

private fun binop(op: String) = when (op) {
    "<->" -> "iff"
    "<-!->" -> "xor"
    "==" -> "="
    "!=" -> throw AssertionError()
    "&&" -> "and"
    "||" -> "or"
    else -> op
}

private fun unop(op: String) = when (op) {
    "!" -> "not"
    "-" -> "-"
    else -> op
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

