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

fun inline(p: Program): Program {
    val (e, t) = inline(p.block.stmts)
    return p.copy(block=Stmt.Block(e.map { it as Stmt } + t.map {it as Stmt}))
}

private fun inline(block: List<Stmt>, _env: Map<Exp.Var, Exp> = mapOf()): Pair<List<Stmt.External>, List<Stmt.Transfer>> {
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
                // FIX: does not handle assignments correctly
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

private fun inline(p: Packet, env: Map<Exp.Var, Exp>) = Packet(p.role, p.params, inline(p.where, env))

private fun inline(exp: Exp, env: Map<Exp.Var, Exp>): Exp {
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

fun prettyPrint(p: Program): String {
    val stmts = pretty(p.block.stmts)
    val typedecls = p.typedecls.map{x->"type ${x.name} = ${pretty(x.definition)})"}
    return(typedecls + stmts).joinToString("\n")
}

fun pretty(block: List<Stmt>): List<String> {
    val res = mutableListOf<String>()
    for (stmt in block) {
        res.addAll(when (stmt) {
            is Stmt.Def.VarDef -> listOf("var ${pretty(stmt.dec.name)}: ${pretty(stmt.dec.type)} = ${pretty(stmt.init)}")
            is Stmt.Def.YieldDef -> listOf("yield " + stmt.packets.joinToString(" ") {pretty(it)})
            is Stmt.Def.JoinDef -> listOf("join " + stmt.packets.joinToString(" ") {pretty(it)})
            is Stmt.Def.JoinManyDef -> listOf("join many ${pretty(stmt.role)}")
            is Stmt.Block -> listOf("{") + pretty(stmt.stmts).map{ "    $it"} + listOf("}")
            is Stmt.Assign -> listOf("${pretty(stmt.target)} = ${pretty(stmt.exp)}")
            is Stmt.Reveal -> listOf("reveal ${pretty(stmt.target)} where ${pretty(stmt.where)}")
            is Stmt.If -> TODO()
            is Stmt.ForYield -> TODO()
            is Stmt.Transfer -> listOf("transfer ${pretty(stmt.amount)} from ${pretty(stmt.from)} to ${pretty(stmt.to)}")
        })
    }
    return res
}

fun pretty(p: Packet): String {
    val params = p.params.joinToString(", ") { x->"${pretty(x.name)}: ${pretty(x.type)}"}
    return "${pretty(p.role)}($params) where ${pretty(p.where)}"
}

fun pretty(exp: Exp): String = when (exp) {
    is Exp.Call -> "${exp.target}(${exp.args.joinToString(", "){ pretty(it)}})"
    is Exp.UnOp -> "(${exp.op}${pretty(exp.operand)})"
    is Exp.BinOp -> "(${pretty(exp.left)} ${exp.op} ${pretty(exp.right)})"
    is Exp.Var -> exp.name
    is Exp.Member -> "${pretty(exp.target)}.${exp.field}"
    is Exp.Cond -> "(${pretty(exp.cond)} ? ${pretty(exp.ifTrue)} : ${pretty(exp.ifFalse)})"
    Exp.UNDEFINED -> "undefined"
    is Exp.Num -> "${exp.n}"
    is Exp.Address -> "${exp.n}"
    is Exp.Q.Y -> TODO()
    is Exp.Q.Let -> TODO()
    is Exp.Q.Transfers -> TODO()
}

fun pretty(texp: TypeExp): String = when (texp) {
    TypeExp.INT -> "int"
    TypeExp.BOOL -> "bool"
    TypeExp.ROLE -> "role"
    TypeExp.ROLESET -> "roleset"
    TypeExp.ADDRESS -> "address"
    TypeExp.UNIT -> "unit"
    is TypeExp.TypeId -> texp.name
    is TypeExp.Subset -> "{${texp.values.joinToString(", ") { pretty(it)}}"
    is TypeExp.Range -> "{${pretty(texp.min)}, ${pretty(texp.max)}}"
}
