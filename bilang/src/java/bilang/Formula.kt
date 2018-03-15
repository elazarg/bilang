package bilang

sealed class Formula {

    data class Q(val exists: Boolean, val v: Exp.Var, val f: Formula) : Formula()

    data class And(val left: Formula, val right: Formula) : Formula()
    data class Or(val left: Formula, val right: Formula) : Formula()
    data class Not(val f: Formula) : Formula()

    data class Atom(val exp: Exp) : Formula()

    data class BVar(val s: String) : Formula()
    object TRUE : Formula()
    object FALSE : Formula()

    companion object {
        fun makeFormula(role: String, block: List<Stmt>, _next: Formula = TRUE): Formula {
            var next: Formula = _next
            for (stmt in block.reversed()) next = when (stmt) {
                is Stmt.Def.VarDef ->
                    And(next, eq(stmt.init, stmt.dec.name))
                is Stmt.Def.YieldDef -> {
                    val packet = stmt.packets[0]
                    Q(packet.role.name == role, packet.params[0].name, next)
                }
                is Stmt.Def.JoinDef -> makeFormula(role, listOf(Stmt.Def.YieldDef(stmt.packets, stmt.hidden)), next)
                is Stmt.Def.JoinManyDef -> throw RuntimeException()
                is Stmt.Block -> makeFormula(role, stmt.stmts, next)
                is Stmt.Assign -> throw RuntimeException()
                is Stmt.Reveal -> next
                is Stmt.If -> {
                    val cond = makeBoolFormula(stmt.cond)
                    Or(
                            And(cond, makeFormula(role, stmt.ifTrue.stmts, next)),
                            And(Not(cond), makeFormula(role, stmt.ifFalse.stmts, next))
                    )
                }
                is Stmt.ForYield -> throw RuntimeException()
                is Stmt.Transfer -> {
                    val w1 = Exp.Var("W1")
                    val w2 = Exp.Var("W2")
                    val minus = Exp.UnOp("-", stmt.amount)
                    And(
                            if (stmt.from == Exp.Var(role)) eq(minus, w1)     else eq(stmt.amount, w2),
                            if (stmt.to == Exp.Var(role)) eq(stmt.amount, w1) else eq(minus, w2)
                    )
                }

            }
            return next
        }

        fun makeBoolFormula(exp: Exp): Formula = when (exp) {
            is Exp.Call -> TODO()
            is Exp.UnOp -> {
                require(exp.op == "!")
                Not(makeBoolFormula(exp))
            }
            is Exp.BinOp -> {
                val left = makeBoolFormula(exp.left)
                val right = makeBoolFormula(exp.right)
                when (exp.op) {
                    "||" -> Or(left, right)
                    "&&" -> And(left, right)
                    else -> throw RuntimeException()
                }
            }
            is Exp.Var -> {
                when (exp.name) {
                    "true" -> TRUE
                    "false" -> FALSE
                    else -> BVar(exp.name)
                }
            }
            is Exp.Member -> TODO()
            is Exp.Cond -> {
                val cond = makeBoolFormula(exp.cond)
                Or(
                        And(cond, makeBoolFormula(exp.ifTrue)),
                        And(Not(cond), makeBoolFormula(exp.ifFalse))
                )
            }
            else -> throw RuntimeException()
        }

        fun eq(left: Exp, right: Exp.Var) = Atom(Exp.BinOp("==", left, right))

    }
}
