package vegas

import vegas.Exp.*
import vegas.Exp.Const.*

typealias OutcomeType = Num

sealed class Tree {
    data class Node(val owner: Role, val env: Env<Const>, val infoset: Int, val edges: List<Map<Var, Const>>, val children: List<Tree>) : Tree()

    data class Leaf(val outcome: Map<Role, OutcomeType>) : Tree()
}

class Extensive(private val name: String, private val desc: String, private val players: List<Role>, private val game: Tree) {
    constructor(prog: ExpProgram) :
            this(prog.name, prog.desc, findRoles(prog.game), TreeMaker(prog.types).fromExp(prog.game))

    fun toEfg(): String = (
        listOf("EFG 2 R ${quote(name)} ${stringList(players.map { it.name })}", quote(desc), "")
                + ExtensivePrinter().toEfg(game, players)
    ).joinToString("\n")

    override fun toString(): String = game.toString()

}

class TreeMaker(private val types: Map<TypeExp.TypeId, TypeExp>) {
    private val infosetCounters = mutableMapOf<Role, Int>()
    private val infosetIds = mutableMapOf<Pair<Role, Env<Const>>, Int>()

    private fun nextInfosetId(role: Role, env: Env<Const>): Int {
        val key = role to env.eraseHidden(role)
        return infosetIds.getOrPut(key) {
            val next = infosetCounters.getOrDefault(role, 0) + 1
            infosetCounters[role] = next
            next
        }
    }

    fun fromExp(ext: Ext, env: Env<Const> = Env()): Tree = when (ext) {
        is Ext.BindSingle -> {
            val q = ext.q
            val subExt = ext.ext
            val role = q.role
            when (ext.kind) {
                Kind.JOIN -> if (q.params.isEmpty()) fromExp(subExt, env.addRole(role))
                             else independent(subExt, listOf(q), env.addRole(role))

                Kind.JOIN_CHANCE -> if (q.params.isEmpty()) fromExp(subExt, env.addRole(role, chance=true))
                                    else independent(subExt, listOf(q), env.addRole(role, chance=true))

                Kind.YIELD -> independent(subExt, listOf(q), env)

                Kind.REVEAL -> {
                    val revealed = env.mapHidden(q){it.value}
                    val names = q.params.map {it.v}
                    val revealedPacket = names.associateWith { revealed.getValue(role, it) }
                    val quit = env.mapHidden(q) { UNDEFINED }
                    val quitPacket = names.associateWith { UNDEFINED }
                    val infoset = nextInfosetId(role, env)
                    val edges = if (env.isChance(role))
                        listOf(revealedPacket)
                    else
                        listOf(revealedPacket, quitPacket)
                    val children = if (env.isChance(role))
                        listOf(fromExp(subExt, revealed))
                    else
                        listOf(fromExp(subExt, revealed), fromExp(subExt, quit))
                    Tree.Node(role, revealed, infoset, edges, children)
                }
            }
        }
        is Ext.Bind -> when (ext.kind) {
            Kind.YIELD -> independent(ext.ext, ext.qs, env)
            Kind.JOIN -> {
                // Join then yield. Is this correct?
                val newEnv = ext.qs.fold(env) { acc, t -> acc.addRole(t.role) }
                independent(ext.ext, ext.qs.filter { it.params.isNotEmpty() }, newEnv)
            }
            Kind.JOIN_CHANCE -> TODO()
            Kind.REVEAL -> TODO()
        }
        is Ext.Value -> Tree.Leaf(desugar(ext.outcome).ts.mapValues { (_, exp) -> eval(exp, env) as OutcomeType })
    }

    private fun enumeratePackets(q: Query, env: Env<Const>): List<Map<Var, Const>> {
        fun combineValues(f: (TypeExp) -> List<Const>) =
            q.params.associate { (v, type) -> Pair(v, f(type)) }.product()

        val undefs = if (env.isChance(q.role)) listOf() else combineValues { listOf<Const>(UNDEFINED) }
        return if (env.quitted(q.role)) undefs
            else (combineValues { enumerateValues(it) }.filter {
                value -> eval(q.where, env.updateHeap(q, value)) == Bool(true)
            } + undefs)
    }

    private fun independent(next: Ext, qs: List<Query>, origEnv: Env<Const>): Tree {
        fun independentRec(qs: List<Query>, env: Env<Const>): Tree {
            if (qs.isEmpty())
                return fromExp(next, env)
            val q = qs.first()
            val infoset = nextInfosetId(q.role, env)
            val edges = enumeratePackets(q, origEnv)
            val children = edges.map { e -> independentRec(qs.drop(1), env.updateHeap(q, e)) }
            return Tree.Node(q.role, env, infoset, edges, children)
        }
        return independentRec(qs, origEnv)
    }

    private fun enumerateValues(t: TypeExp): List<Const> = when (t) {
        is TypeExp.Subset -> t.values.toList()
        TypeExp.BOOL -> listOf(Bool(true), Bool(false))
        is TypeExp.Hidden -> enumerateValues(t.type).map { hide(it) }
        is TypeExp.TypeId -> enumerateValues(types.getValue(t))
        else -> throw NotImplementedError("cannot enumerate $t; Only small, finite domains are supported")
    }
}

private fun hide(v: Const): Const = when (v) {
    UNDEFINED -> UNDEFINED
    else -> Hidden(v)
}

fun eval(exp: Exp, env: Env<Const>): Const {
    fun eval(exp: Exp) = eval(exp, env)
    return when (exp) {
        is Call -> when (exp.target.name) {
            "alldiff" -> Bool(exp.args.map {eval(it)}.distinct().size == exp.args.size)
            else -> TODO()
        }
        is UnOp -> when (exp.op) {
            "-" -> Num(-(eval(exp.operand) as Num).n)
            "!" -> Bool(!(eval(exp.operand) as Bool).truth)
            "isUndefined" -> Bool(eval(exp.operand) == UNDEFINED)
            "isDefined" -> Bool(eval(exp.operand) != UNDEFINED)
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
            when (val cond = eval(exp.cond)) {
                is Bool -> if (cond.truth) eval(exp.ifTrue) else eval(exp.ifFalse)
                else -> throw AssertionError()
            }
        }
        UNDEFINED -> UNDEFINED
        is Address -> exp
        is Num -> exp
        is Bool -> exp
        is Hidden -> exp
        is Let -> eval(exp.exp, env + Pair(exp.dec.v, eval(exp.init)))
    }
}

class ExtensivePrinter(private val outcomeToPayoff: (Role, OutcomeType) -> Int = {_, v -> v.n}) {
    private var outcomeNumber: Int = 0

    fun toEfg(t: Tree, roleOrder: List<Role>): List<String> = when (t) {
        is Tree.Node -> {
            if (t.env.isChance(t.owner)) { // FIX: this should be known statically, not by env
                val nodeName = ""
                val infoset: Int = t.infoset
                val infosetName = ""
                val actionsAndProbabilities = ""  // e.g. '{ "true" 1/2 "false" 1/2 }'
                val actionNamesForInfoset: String = t.edges.joinToString(" ", "{ ", " }") {
                    v -> quote(v.values.joinToString("&") { valueToName(it) }) + " 1/" + t.edges.size
                }
                val payoffs = 0
                listOf("c ${quote(nodeName)} $infoset ${quote(infosetName)} $actionsAndProbabilities $actionNamesForInfoset $payoffs") +
                        t.children.flatMap { toEfg(it, roleOrder) }
            } else {
                val nodeName = ""
                val owner: Int = roleOrder.indexOf(t.owner) + 1 // TODO: why not env.getValue(t.owner).n?
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
        }
        is Tree.Leaf -> {
            val name = ""
            val outcome: Int = outcomeNumber // TODO: what is this exactly? must it be sequential?
            // Seems like outcomes are "named outcomes" and should define the outcome uniquely
            outcomeNumber += 1
            val nameOfOutcome = ""
            val payoffs = roleOrder.map { outcomeToPayoff(it, t.outcome.getValue(it)) }.joinToString(" ", "{ ", " }")
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

// Env extensions

private fun Env<Const>.mapHidden(q: Query, f: (Hidden) -> Const) = copy(h =
    h.mapValues { (rv, k) ->
        if (k is Hidden && rv.first == q.role
                && rv.second in q.params.map { (v, _) -> v }) f(k) else k
    }
)

private fun Env<Const>.eraseHidden(role: Role) = copy(h =
    h.mapValues { (rv, k) ->
        if (k is Hidden && rv.first != role) Hidden(UNDEFINED) else k
    }
)

private fun Env<Const>.updateHeap(q: Query, newEnv: Map<Var, Const>): Env<Const> = copy(h =
    h + newEnv.map { (v, k) -> Pair(Pair(q.role, v), k) }
)

private fun Env<Const>.addRole(role: Role, chance: Boolean = false): Env<Const> {
    val address = if (chance) 0 else
        (1 + (g.values.maxOfOrNull { (it as? Address)?.n ?: 0 } ?: 0))
    return this withRole Pair(role, Address(address))
}

private fun Env<Const>.quitted(role: Role): Boolean = h.any { (rv, k) -> rv.first == role && k == UNDEFINED }

private fun Env<Const>.isChance(role: Role) = this.getValue(role) == Address(0)
