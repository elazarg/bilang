package bilang

val TRUE = Exp.Var("true")

fun makeFormula(block: List<Stmt.External>, _next: Exp = TRUE): Exp {
    var next: Exp = _next
    for (stmt in block.reversed()) next = when (stmt) {
        is Stmt.YieldDef -> {
            var n = next
            for (p in stmt.packets.reversed())
                n = Exp.Q.Y(p, n, true)
            for (p in stmt.packets.reversed())
                n = makeFormula(listOf(Stmt.Reveal(p.params[0].name, p.where)), n)
            n
        }
        is Stmt.JoinDef ->  {
            var n = next
            for (p in stmt.packets.reversed())
                n = Exp.Q.Y(p, makeFormula(listOf(Stmt.YieldDef(stmt.packets, stmt.hidden)), next))
            n
        }
        is Stmt.JoinManyDef -> throw RuntimeException()
        else -> TODO()
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
            is Stmt.VarDef -> env[stmt.dec.name] = inline(stmt.init, env)
            is Stmt.Assign -> env[stmt.target] = inline(stmt.exp, env)
            is Stmt.YieldDef -> external.add(stmt.copy(packets=stmt.packets.map { inline(it, env) }))
            is Stmt.JoinDef -> external.add(stmt.copy(packets=stmt.packets.map { inline(it, env) }))
            is Stmt.JoinManyDef -> external.add(stmt)
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
        is Exp.Q.Transfers -> exp.copy(ts=exp.ts.map{it.copy(amount=inline(it.amount, env))})
    }
}

fun prettyPrint(p: Program): String {
    val stmts = pretty(p.block.stmts)
    val typedecls = p.typedecls.map{"type ${it.name} = ${pretty(it.definition)})"}
    return(typedecls + stmts).joinToString("\n")
}

fun pretty(block: List<Stmt>): List<String> = block.flatMap { pretty(it) }

private fun pretty(stmt: Stmt) = when (stmt) {
    is Stmt.VarDef -> listOf("var ${pretty(stmt.dec.name)}: ${pretty(stmt.dec.type)} = ${pretty(stmt.init)};")
    is Stmt.YieldDef -> listOf("yield ${if (stmt.hidden) "hidden " else ""}${stmt.packets.joinToString(" ") { pretty(it) }};")
    is Stmt.JoinDef -> listOf("join ${stmt.packets.joinToString(" ") { pretty(it) }};")
    is Stmt.JoinManyDef -> listOf("join many ${pretty(stmt.role)};")
    is Stmt.Block -> listOf("{") + pretty(stmt.stmts).map { "    $it" } + listOf("}")
    is Stmt.Assign -> listOf("${pretty(stmt.target)} = ${pretty(stmt.exp)}")
    is Stmt.Reveal -> listOf("reveal ${pretty(stmt.target)} where ${pretty(stmt.where)}")
    is Stmt.If -> listOf("if (${pretty(stmt.cond)})") + pretty(listOf(stmt.ifTrue)) + listOf("else ") + pretty(listOf(stmt.ifFalse))
    is Stmt.ForYield -> TODO()
    is Stmt.Transfer -> listOf("transfer ${pretty(stmt.amount)} from ${pretty(stmt.from)} to ${pretty(stmt.to)};")
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
fun inlineWhere(p: Program): Program = p.copy (block=Stmt.Block(p.block.stmts.flatMap { inlineWhere(it) }))

fun inlineWhere(s: Stmt): List<Stmt> = when (s) {
    is Stmt.JoinDef -> {
        val hides: List<Stmt> = s.packets.map { Stmt.JoinDef(listOf(Packet(it.role, listOf(), TRUE)), true) }
        val reveals: List<Stmt> = if (s.hidden) listOf() else s.packets.flatMap { p -> p.params.map { vd -> Stmt.Reveal(vd.name, TRUE) } }
        val wheres: List<Stmt> = s.packets.flatMap { inlineWhere(it) }
        hides + reveals + wheres
    }
    is Stmt.YieldDef -> {
        val hides: List<Stmt> = s.packets.flatMap { p -> p.params.map { vd -> Stmt.YieldDef(listOf(Packet(p.role, listOf(vd), TRUE)), true) } }
        val reveals: List<Stmt> = if (s.hidden) listOf() else s.packets.flatMap { p -> p.params.map { vd -> Stmt.Reveal(vd.name, TRUE) } }
        val wheres: List<Stmt> = s.packets.flatMap { inlineWhere(it) }
        hides + reveals + wheres
    }
    is Stmt.Reveal -> listOf(s.copy(where = TRUE),
            Stmt.Assign(s.target, Exp.Cond(s.where, s.target, Exp.UNDEFINED)))
    is Stmt.Block -> s.stmts.flatMap { inlineWhere(it) }

    else -> listOf(s)
}

fun inlineWhere(p: Packet): List<Stmt> = p.params.map {
    vd -> Stmt.VarDef(vd, Exp.Cond(p.where, vd.name, Exp.UNDEFINED))
}
