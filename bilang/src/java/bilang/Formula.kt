package bilang

fun makeFormula(block: List<Stmt>, _next: Exp = Exp.Var("true")): Exp {
    var next: Exp = _next
    for (stmt in block.reversed()) next = when (stmt) {
        is Stmt.Def.VarDef -> Exp.Q.Let(stmt.dec, stmt.init)
        is Stmt.Def.YieldDef -> {
            var n = next
            for (p in stmt.packets.reversed())
                n = Exp.Q.Y(p, n, true)
            for (p in stmt.packets.reversed())
                n = makeFormula(listOf(Stmt.Reveal(p.params[0].name, p.where)), n)
            n
        }
        is Stmt.Def.JoinDef ->  {
            var n = next
            for (p in stmt.packets.reversed())
                n = Exp.Q.Y(p, makeFormula(listOf(Stmt.Def.YieldDef(stmt.packets, stmt.hidden)), next))
            n
        }
        is Stmt.Def.JoinManyDef -> throw RuntimeException()
        is Stmt.Block -> makeFormula(stmt.stmts, next)
        is Stmt.Assign -> throw RuntimeException()
        is Stmt.Reveal -> next
        is Stmt.If -> Exp.Cond(stmt.cond,
                makeFormula(stmt.ifTrue.stmts, next),
                makeFormula(stmt.ifFalse.stmts, next)
        )
        is Stmt.ForYield -> throw RuntimeException()
        is Stmt.Transfer -> Exp.Q.Transfers((next as Exp.Q.Transfers).ts + stmt) //FIX
    }
    return next
}

fun inline(block: List<Stmt>, _env: Map<Exp.Var, Exp> = mapOf()): Pair<List<Stmt.External>, List<Stmt.Transfer>> {
    val env = _env.toMutableMap()
    val external: MutableList<Stmt.External> = mutableListOf()
    val transfers: MutableList<Stmt.Transfer> = mutableListOf()
    for (stmt in block) {
        when (stmt) {
            is Stmt.Def.VarDef -> env[stmt.dec.name] = inline(stmt.init, env)
            is Stmt.Assign -> env[stmt.target] = inline(stmt.exp, env)
            is Stmt.Def.YieldDef -> external.add(stmt.copy(packets=stmt.packets.map { inline(it, env) }))
            is Stmt.Def.JoinDef -> external.add(stmt.copy(packets=stmt.packets.map { inline(it, env) }))
            is Stmt.Def.JoinManyDef -> external.add(stmt)
            is Stmt.Reveal -> external.add(stmt.copy(where=inline(stmt.where, env)))
            is Stmt.Block -> {
                val (e, t) = inline(stmt.stmts, env)
                external.addAll(e)
                transfers.addAll(t)
            }
            is Stmt.If -> {
                // FIX: does not handle assignments
                val cond = inline(stmt.cond, env)
                val (et, _tt) = inline(stmt.ifTrue.stmts, env)
                val (ef, _tf) = inline(stmt.ifFalse.stmts, env)
                if (et.isNotEmpty() || ef.isNotEmpty()) throw RuntimeException()
                val tt = _tt.map {it.copy(amount=Exp.Cond(cond, it.amount, Exp.Num(0)))}
                val tf = _tf.map {it.copy(amount=Exp.Cond(cond, Exp.Num(0), it.amount))}
                transfers.addAll(tt)
                transfers.addAll(tf)
            }
            is Stmt.ForYield -> throw RuntimeException()
            is Stmt.Transfer -> transfers.add(stmt.copy(amount=inline(stmt.amount, env)))
        }
    }
    return Pair(external, transfers)
}

fun inline(p: Packet, env: Map<Exp.Var, Exp>) = Packet(p.role, p.params, inline(p.where, env))

fun inline(exp: Exp, env: Map<Exp.Var, Exp>): Exp {
    fun inline(e: Exp) = inline(e, env)
    return when (exp) {
        is Exp.Call -> exp.copy(args=exp.args.map {inline(it)})
        is Exp.UnOp -> exp.copy(operand=inline(exp.operand))
        is Exp.BinOp -> exp.copy(left=inline(exp.left), right=inline(exp.right))
        is Exp.Var -> env.getOrDefault(exp, exp)
        is Exp.Member -> exp
        is Exp.Cond -> exp.copy(cond=inline(exp.cond), ifTrue=inline(exp.ifTrue), ifFalse=inline(exp.ifFalse))
        Exp.UNDEFINED, is Exp.Num, is Exp.Address -> exp
        is Exp.Q.Y -> TODO()
        is Exp.Q.Let -> TODO()
        is Exp.Q.Transfers -> TODO()
    }
}

