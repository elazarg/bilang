package bilang

import bilang.Exp.*
import bilang.Exp.Const.*

sealed class Tree {
    data class Node(val owner: String, val env: Env, val infoset: Int, val edges: List<Map<Var, Const>>, val children: List<Tree>) : Tree()

    data class Leaf(val payoff: Map<String, Num>) : Tree()
}

class Extensive(private val name: String, private val desc: String, private val players: List<String>, private val game: Tree) {
    constructor(name: String, prog: ExpProgram) :
            this(name, prog.desc, findRoles(prog.game), TreeMaker(prog.types).fromExp(prog.game))

    fun toEfg(): String = (
        listOf("EFG 2 R ${quote(name)} ${stringList(players)}", quote(desc), "")
                + ExtensivePrinter().toEfg(game, players)
    ).joinToString("\n")

    override fun toString(): String = game.toString()

}

class TreeMaker(val types: Map<String, TypeExp>) {
    fun fromExp(ext: Ext, env: Env = Env()): Tree = when (ext) {
        is Ext.BindSingle -> {
            val q = ext.q
            val subExt = ext.ext
            when (ext.kind) {
                Kind.JOIN -> fromExp(subExt, env.addRole(q.role)) // independent(subExt, env.addRole(q.role), listOf(q))
                Kind.YIELD -> independent(subExt, env, listOf(q))
                Kind.REVEAL -> {
                    val revealed = env.mapHidden(q){it.value}
                    val revealedPacket = q.params.map { Pair(it.name, revealed.getValue(q.role, it.name.name)) }.toMap()
                    val quit = env.mapHidden(q){UNDEFINED}
                    val quitPacket = q.params.map { Pair(it.name, UNDEFINED) }.toMap()
                    val infoset = UniqueHash.of(env.eraseHidden(q.role.name))
                    Tree.Node(q.role.name, revealed, infoset,
                            listOf(revealedPacket, quitPacket),
                            listOf(fromExp(subExt, revealed), fromExp(subExt, quit))
                        )
                }
                Kind.MANY -> TODO()
            }
        }
        is Ext.Bind -> when (ext.kind) {
            Kind.YIELD -> independent(ext.ext, env, ext.qs)
            Kind.JOIN -> {
                // Naive. Join then yield. Is this correct?
                val newEnv = ext.qs.fold(env) { acc, t -> acc.addRole(t.role) }
                independent(ext.ext, newEnv, ext.qs)
            }
            Kind.REVEAL -> TODO()
            Kind.MANY -> TODO()
        }
        is Ext.Value -> Tree.Leaf((eval(ext.exp, env)).ts as Map<String, Num>)
    }

    private fun enumeratePackets(q: Query, env: Env): List<Map<Var, Const>> {
        fun combineValues(f: (VarDec) -> List<Const>) =
                q.params.map { d -> Pair(d.name, f(d)) }.toMap().product()

        return combineValues { listOf<Const>(UNDEFINED) }.let { undefs ->
            if (env.quitted(q.role)) undefs
            else (combineValues { enumerateValues(it.type) }.filter {
                value -> eval(q.where, env.updateHeap(q, value)) == Bool(true)
            } + undefs)
        }
    }

    private fun independent(next: Ext, origEnv: Env, qs: List<Query>): Tree {
        fun independentRec(qs: List<Query>, env: Env): Tree {
            if (qs.isEmpty())
                return fromExp(next, env)
            val q = qs.first()
            val infoset = UniqueHash.of(origEnv.eraseHidden(q.role.name))
            val edges = enumeratePackets(q, origEnv)
            val children = edges.map { e -> independentRec(qs.drop(1), env.updateHeap(q, e)) }
            return Tree.Node(q.role.name, env, infoset, edges, children)
        }
        return independentRec(qs, origEnv)
    }

    private fun enumerateValues(t: TypeExp): List<Const> = when (t) {
        is TypeExp.Subset -> t.values.toList()
        TypeExp.BOOL -> listOf(Bool(true), Bool(false))
        is TypeExp.Hidden -> enumerateValues(t.type).map { hide(it) }
        is TypeExp.TypeId -> enumerateValues(types.getValue(t.name))
        else -> throw AssertionError("cannot enumerate $t")
    }
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
            "isUndefined" -> Bool(eval(exp.operand) == UNDEFINED)
            else -> throw AssertionError()
        }
        is BinOp -> {
            val (left, right) = Pair(eval(exp.left), eval(exp.right))
            val res: Const = when {
                exp.op == "==" -> Bool(left == right)
                exp.op == "!=" -> Bool(left != right)
                exp.op == "<->" -> Bool(left == right)
                exp.op == "<-!->" -> Bool(left != right)
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
    }
}

fun eval(exp: Payoff.Value, env: Env): Payoff.Value =
        Payoff.Value(exp.ts.map { (k, v) -> Pair(k, eval(v, env) as Num) }.toMap())

class ExtensivePrinter {
    private var outcomeNumber: Int = 0

    fun toEfg(t: Tree, roleOrder: List<String>): List<String> = when (t) {
        is Tree.Node -> {
            val nodeName = ""
            val owner: Int = roleOrder.indexOf(t.owner) + 1
            // TODO: remove last assignment
            val infoset: Int = t.infoset
            val infosetName = ""
            val actionNamesForInfoset: String = stringList(t.edges.map { v -> v.values.joinToString("&") { valueToName(it) } })
            val outcome = 0
            val nameOfOutcome = ""
            val payoffs = 0
            listOf("p ${quote(nodeName)} $owner $infoset ${quote(infosetName)} $actionNamesForInfoset $payoffs") +
                    t.children.flatMap { toEfg(it, roleOrder) }
        }
        is Tree.Leaf -> {
            val name = ""
            val outcome: Int = outcomeNumber // TODO: what is this exactly? must it be sequential?
            // Seems like outcomes are "named payoffs" and should define the payoff uniquely
            outcomeNumber += 1
            val nameOfOutcome = ""
            val payoffs = roleOrder.map { t.payoff.getValue(it).n }.joinToString(" ", "{ ", " }")
            listOf("t ${quote(name)} $outcome ${quote(nameOfOutcome)} $payoffs")
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

private fun quote(name: String) = '"' + name + '"'

private fun stringList(ss: Iterable<String>) = ss.joinToString(" ", "{ ", " }") { quote(it) }


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
