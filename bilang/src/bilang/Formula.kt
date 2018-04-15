package bilang
import bilang.Exp.*
import bilang.Stmt.*

val TRUE = Var("true")

fun makeFormula(block: List<External>, _next: Exp = TRUE): Exp {
    var next: Exp = _next
    for (stmt in block.reversed()) next = when (stmt) {
        is YieldDef -> {
            var n = next
            for (p in stmt.packets.reversed())
                n = Ext.Yield(p, n, true)
            for (p in stmt.packets.reversed())
                n = makeFormula(listOf(Reveal(p.params[0].name, p.where)), n)
            n
        }
        is JoinDef ->  {
            var n = next
            for (p in stmt.packets.reversed())
                n = Ext.Yield(p, makeFormula(listOf(YieldDef(stmt.packets, stmt.hidden)), next))
            n
        }
        is JoinManyDef -> throw RuntimeException()
        else -> TODO()
    }
    return next
}

fun inline(p: Program): Program {
    val (e, t) = inline(p.block.stmts)
    return p.copy(block=Block(e.map { it as Stmt } + t.map {it as Stmt}))
}

private fun inline(block: List<Stmt>, _env: Map<Var, Exp> = mapOf()): Pair<List<External>, List<Transfer>> {
    val env = _env.toMutableMap()
    val external: MutableList<External> = mutableListOf()
    val transfers: MutableList<Transfer> = mutableListOf()
    for (stmt in block) {
        when (stmt) {
            is VarDef -> env[stmt.dec.name] = inline(stmt.init, env)
            is Assign -> env[stmt.target] = inline(stmt.exp, env)
            is YieldDef -> external.add(stmt.copy(packets=stmt.packets.map { inline(it, env) }))
            is JoinDef -> external.add(stmt.copy(packets=stmt.packets.map { inline(it, env) }))
            is JoinManyDef -> external.add(stmt)
            is Reveal -> external.add(stmt.copy(where=inline(stmt.where, env)))
            is Block -> {
                val (e, t) = inline(stmt.stmts, env)
                external.addAll(e)
                transfers.addAll(t)
            }
            is If -> {
                // FIX: does not handle assignments correctly
                val cond = inline(stmt.cond, env)
                val (et, _tt) = inline(listOf(stmt.ifTrue), env)
                val (ef, _tf) = inline(listOf(stmt.ifFalse), env)
                if (et.isNotEmpty() || ef.isNotEmpty()) throw RuntimeException()
                val tt = _tt.map {it.copy(amount=Cond(cond, it.amount, Num(0)))}
                val tf = _tf.map {it.copy(amount=Cond(cond, Num(0), it.amount))}
                transfers.addAll(tt)
                transfers.addAll(tf)
            }
            is ForYield -> throw RuntimeException()
            is Transfer -> transfers.add(stmt.copy(amount=inline(stmt.amount, env)))
        }
    }
    return Pair(external, transfers)
}

private fun inline(p: Packet, env: Map<Var, Exp>) = Packet(p.role, p.params, inline(p.where, env))

private fun inline(exp: Exp, env: Map<Var, Exp>): Exp {
    fun inline(e: Exp) = inline(e, env)
    return when (exp) {
        is Call -> exp.copy(args=exp.args.map {inline(it)})
        is UnOp -> exp.copy(operand=inline(exp.operand))
        is BinOp -> exp.copy(left=inline(exp.left), right=inline(exp.right))
        is Var -> env.getOrDefault(exp, exp)
        is Member -> exp
        is Cond -> {
            val cond = inline(exp.cond)
            val ifTrue = inline(exp.ifTrue)
            if (cond == TRUE) ifTrue
            else exp.copy(cond=cond, ifTrue= ifTrue, ifFalse=inline(exp.ifFalse))
        }
        UNDEFINED, is Num, is Address, is Exp.Bool, is Exp.Hidden -> exp
        is Q -> TODO()
        is Ext -> TODO()
    }
}

fun prettyPrint(p: Program): String {
    val stmts = pretty(p.block.stmts)
    val typedecls = p.typedecls.map{"type ${it.name} = ${pretty(it.definition)}"}
    return(typedecls + stmts).joinToString("\n")
}

fun pretty(block: List<Stmt>): List<String> = block.flatMap { pretty(it) }

private fun pretty(stmt: Stmt) = when (stmt) {
    is VarDef -> listOf("var ${pretty(stmt.dec.name)}: ${pretty(stmt.dec.type)} = ${pretty(stmt.init)};")
    is YieldDef -> listOf("yield ${if (stmt.hidden) "hidden " else ""}${stmt.packets.joinToString(" ") { pretty(it) }};")
    is JoinDef -> listOf("join ${stmt.packets.joinToString(" ") { pretty(it) }};")
    is JoinManyDef -> listOf("join many ${pretty(stmt.role)};")
    is Block -> listOf("{") + pretty(stmt.stmts).map { "    $it" } + listOf("}")
    is Assign -> listOf("${pretty(stmt.target)} = ${pretty(stmt.exp)}")
    is Reveal -> listOf("reveal ${pretty(stmt.target)} where ${pretty(stmt.where)}")
    is If -> listOf("if (${pretty(stmt.cond)})") + pretty(listOf(stmt.ifTrue)) + listOf("else ") + pretty(listOf(stmt.ifFalse))
    is ForYield -> TODO()
    is Transfer -> listOf("transfer ${pretty(stmt.amount)} from ${pretty(stmt.from)} to ${pretty(stmt.to)};")
}

fun pretty(p: Packet): String {
    val params = p.params.joinToString(", ") { x->"${pretty(x.name)}: ${pretty(x.type)}"}
    return "${pretty(p.role)}($params) where ${pretty(p.where)}"
}

fun pretty(exp: Exp): String = when (exp) {
    is Call -> "${exp.target}(${exp.args.joinToString(", "){ pretty(it)}})"
    is UnOp -> "(${exp.op}${pretty(exp.operand)})"
    is BinOp -> "(${pretty(exp.left)} ${exp.op} ${pretty(exp.right)})"
    is Var -> exp.name
    is Member -> "${pretty(exp.target)}.${exp.field}"
    is Cond -> "(${pretty(exp.cond)} ? ${pretty(exp.ifTrue)} : ${pretty(exp.ifFalse)})"
    UNDEFINED -> "undefined"
    is Num -> "${exp.n}"
    is Bool -> "${exp.truth}"
    is Address -> "${exp.n}"
    is Ext -> TODO()
    is Q -> TODO()
    is Exp.Hidden -> TODO()
}

fun pretty(texp: TypeExp): String = when (texp) {
    TypeExp.INT -> "int"
    TypeExp.BOOL -> "bool"
    TypeExp.ROLE -> "role"
    TypeExp.ROLESET -> "roleset"
    TypeExp.ADDRESS -> "address"
    TypeExp.UNIT -> "unit"
    is TypeExp.TypeId -> texp.name
    is TypeExp.Hidden -> "hidden[${pretty(texp.type)}]"
    is TypeExp.Subset -> "{${texp.values.joinToString(", ") { pretty(it)}}}"
    is TypeExp.Range -> "{${pretty(texp.min)}, ${pretty(texp.max)}}"
}


fun inlineWhere(p: Program): Program = p.copy (block=Block(p.block.stmts.flatMap { inlineWhere(it) }))

fun inlineWhere(s: Stmt): List<Stmt> = when (s) {
    is JoinDef -> hideReveal(s.packets, s.hidden) { p ->
        listOf(JoinDef(listOf(Packet(p.role, listOf(), TRUE)), true))
    }
    is YieldDef -> hideReveal(s.packets, s.hidden) { p ->
        p.params.map { vd -> YieldDef(listOf(Packet(p.role, listOf(vd), TRUE)), true) }
    }
    is Reveal -> listOf(s.copy(where = TRUE),
            Assign(s.target, Cond(s.where, s.target, UNDEFINED)))
    is Block -> s.stmts.flatMap { inlineWhere(it) }

    else -> listOf(s)
}

fun inlineWhere(p: Packet): List<Stmt> = p.params.map {
    vd -> VarDef(vd, Cond(p.where, vd.name, UNDEFINED))
}

private fun hideReveal(packets: List<Packet>, hidden: Boolean, fp: (Packet) -> List<Stmt>) : List<Stmt> {
    val hides: List<Stmt> = packets.flatMap { fp(it) }
    val reveals: List<Stmt> = if (hidden) listOf() else packets.flatMap { p -> p.params.map { vd -> Reveal(vd.name, TRUE) } }
    val wheres: List<Stmt> = packets.flatMap { inlineWhere(it) }
    return hides + reveals + wheres
}