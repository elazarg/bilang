package bilang

import bilang.Exp.*

sealed class Tree {
    data class Node(val owner: String, val env: Env, val children: Map<Map<Var, Const>, Tree>) : Tree()

    data class Leaf(val payoff: Map<Var, Num>) : Tree()
}

class Extensive(private val name: String, private val desc: String, private val players: List<String>, private val game: Tree) {
    constructor(name: String, prog: ExpProgram) :
            this(name, prog.desc, findRoles(prog.game), TreeMaker(prog.types).fromExp(prog.game))

    fun toEfg(): String = (
        listOf("EFG 2 R ${q(name)} ${stringList(players)}", q(desc), "")
                + ExtensivePrinter().toEfg(game, players)
    ).joinToString("\n")

    override fun toString(): String = game.toString()

}

class TreeMaker(val types: Map<String, TypeExp>) {
    fun fromExp(ext: Ext, env: Env = Env()): Tree = when (ext) {
        is Ext.BindSingle -> {
            fun subtree(e: Env) = fromExp(ext.ext, e)
            when (ext.kind) {
                Kind.JOIN -> subtree(env.addRole(ext.q.role)) // TODO: Handle joins with parameters and concurrent joins
                Kind.YIELD -> {
                    fun combineValues(f: (VarDec) -> List<Const>) = ext.q.params.map { d -> Pair(d.name, f(d)) }.toMap().product()

                    val children = combineValues { listOf<Const>(UNDEFINED) }.let { undefs ->
                        if (env.quitted(ext.q.role)) undefs
                        else (combineValues { enumerateValues(it.type) }.filter {
                            eval(ext.q.where, env.updateHeap(ext.q, it)) == Bool(true)
                        } + undefs)
                    }.map { Pair(it, subtree(env.updateHeap(ext.q, it))) }.toMap()
                    Tree.Node(ext.q.role.name, env, children)
                }
                Kind.REVEAL -> {
                    val revealed = env.mapHidden(ext.q){it.value}
                    val revealedPacket = ext.q.params.map { Pair(it.name, revealed.getValue(ext.q.role, it.name.name)) }.toMap()
                    val quit = env.mapHidden(ext.q){UNDEFINED}
                    val quitPacket = ext.q.params.map { Pair(it.name, UNDEFINED) }.toMap()
                    Tree.Node(ext.q.role.name, revealed, mapOf(
                            Pair(revealedPacket, subtree(revealed)),
                            Pair(quitPacket, subtree(quit))
                        )
                    )
                }
                Kind.MANY -> TODO()
            }
        }
        is Ext.Bind -> {
            TODO("FIX: infinite recursion")
            val ext1 = independent(ext.kind, ext.qs, ext.ext)
            fromExp(ext1.qs.fold(ext1.ext) { acc, q -> Ext.BindSingle(ext1.kind, q, acc) }, env)
        }
        is Ext.Value -> Tree.Leaf((eval(ext.exp, env) as Payoff).ts as Map<Var, Num>)
    }

    private fun enumerateValues(t: TypeExp): List<Const> = when (t) {
        is TypeExp.Subset -> t.values.toList()
        TypeExp.BOOL -> listOf(Bool(true), Bool(false))
        is TypeExp.Hidden -> enumerateValues(t.type).map { hide(it) }
        is TypeExp.TypeId -> enumerateValues(types.getValue(t.name))
        else -> throw AssertionError("cannot enumerate $t")
    }
}

fun independent(kind: Kind, qs: List<Query>, ext: Ext): Ext.Bind {
    val reveal = Ext.Bind(Kind.REVEAL, qs.map { it.copy(params = it.params.filterNot { it.type is TypeExp.Hidden }) }, ext)
    return Ext.Bind(kind, qs.map { it.copy(params = it.params.map { p -> p.copy(type = hide(p.type)) }) },
            if (qs.any { it.params.isNotEmpty() }) reveal else ext)
}

private fun hide(v: Const): Const = when (v) {
    UNDEFINED -> UNDEFINED
    else -> Hidden(v)
}

fun eval(exp: Exp, env: Env): Const {
    fun eval(exp: Exp) = eval(exp, env)
    return when (exp) {
        is Call -> TODO()
        is UnOp -> when (exp.op) {
            "-" -> Num(-(eval(exp.operand) as Num).n)
            "!" -> Bool(!(eval(exp.operand) as Bool).truth)
            else -> throw AssertionError()
        }
        is BinOp -> {
            val (left, right) = Pair(eval(exp.left), eval(exp.right))
            val res: Const = when {
                exp.op == "==" -> Bool(left == right)
                exp.op == "!=" -> Bool(left != right)
                left is Num && right is Num -> when (exp.op) {
                    "+" -> Num(left.n + right.n)
                    "-" -> Num(left.n - right.n)
                    "*" -> Num(left.n * right.n)
                    "/" -> Num(left.n / right.n)
                    "<" -> Bool(left.n < right.n)
                    "<=" -> Bool(left.n <= right.n)
                    ">" -> Bool(left.n > right.n)
                    ">=" -> Bool(left.n >= right.n)
                    else -> throw AssertionError()
                }
                left is Bool && right is Bool -> when (exp.op) {
                    "&&" -> Bool(left.truth && right.truth)
                    "||" -> Bool(left.truth || right.truth)
                    else -> throw AssertionError()
                }
                else -> throw AssertionError("$left ${exp.op} $right")
            }
            res
        }
        is Var -> env.getValue(exp)
        is Member -> env.getValue(exp.target, exp.field)
        is Cond -> {
            val cond = eval(exp.cond)
            when (cond) {
                is Bool -> if (cond.truth) eval(exp.ifTrue) else eval(exp.ifFalse)
                else -> throw AssertionError()
            }
        }
        UNDEFINED -> UNDEFINED
        is Address -> exp
        is Num -> exp
        is Bool -> exp
        is Hidden -> exp
        is Let -> eval(exp.exp, env + Pair(exp.dec.name, eval(exp.init)))
        is Payoff -> Payoff(exp.ts.map { (k, v) -> Pair(k, eval(v) as Num) }.toMap())
    }
}

class ExtensivePrinter {
    private var outcomeNumber: Int = 0

    fun toEfg(t: Tree, roleOrder: List<String>): List<String> = when (t) {
        is Tree.Node -> {
            val (values, children) = t.children.entries.map { it.toPair() }.unzip()
            val nodeName = ""
            val owner: Int = roleOrder.indexOf(t.owner) + 1
            // TODO: remove last assignment
            val infoset: Int = UniqueHash.of(t.env.eraseHidden(t.owner)) // FIX: do we consider current choice???
            val infosetName = ""
            val actionNamesForInfoset: String = stringList(values.map { v -> v.values.joinToString("&") { valueToName(it) } })
            val outcome = 0
            val nameOfOutcome = ""
            val payoffs = 0
            listOf("p ${q(nodeName)} $owner $infoset ${q(infosetName)} $actionNamesForInfoset $payoffs") +
                    children.flatMap { toEfg(it, roleOrder) }
        }
        is Tree.Leaf -> {
            val name = ""
            val outcome: Int = outcomeNumber // TODO: what is this exactly? must it be sequential?
            // Seems like outcomes are "named payoffs" and should define the payoff uniquely
            outcomeNumber += 1
            val nameOfOutcome = ""
            val payoffs = roleOrder.map { t.payoff.getValue(Var(it)).n }.joinToString(" ", "{ ", " }")
            listOf("t ${q(name)} $outcome ${q(nameOfOutcome)} $payoffs")
        }
    }

    private fun valueToName(v: Const): String = when (v) {
        is Bool -> v.truth.toString()
        is Num -> v.n.toString()
        is Hidden -> "Hidden(${valueToName(v.value)})"
        UNDEFINED -> "None"
        else -> throw Exception(v.toString())
    }
}

private fun q(name: String) = '"' + name + '"'

private fun stringList(ss: Iterable<String>) = ss.joinToString(" ", "{ ", " }") { q(it) }


data class Env(private val g: Map<Var, Const>, private val h: Map<Pair<Var, Var>, Const>) {
    constructor(): this(mapOf(), mapOf())

    operator fun plus(p: Pair<Var, Const>) = Env(g + p, h)

    fun mapHidden(q: Query, f: (Hidden) -> Const) = copy(h=
        h.mapValues { (rv, k) ->
            if (k is Hidden && rv.first == q.role
                    && q.params.map { it.name.name }.contains(rv.second.name)) f(k) else k
        }
    )

    fun eraseHidden(role: String) = copy(h=
        h.mapValues { (rv, k) ->
            if (k is Hidden && rv.first.name != role) Hidden(UNDEFINED) else k
        }
    )

    fun updateHeap(q: Query, newEnv: Map<Var, Const>): Env {
        val mh = h.toMutableMap()
        mh.putAll(newEnv.map { (v, k) -> Pair(Pair(q.role, v), k) })
        return copy(h=mh.toMap())
    }

    fun addRole(role: Var) = this + Pair(role,
            Address(1 + (g.values.map { (it as? Address)?.n ?: 0 }.max() ?: 0))
    )

    fun getValue(v: Var) = g.getValue(v)
    fun getValue(role: String, field: String) = h.getValue(Pair(Var(role), Var(field)))
    fun getValue(role: Var, field: String) = h.getValue(Pair(role, Var(field)))
    fun quitted(role: Exp.Var): Boolean = h.any { (rv, k) -> rv.first == role && k == UNDEFINED }
}
