package bilang
import bilang.Exp.*

sealed class Tree {
    data class Node(val owner: String, val h: Map<Pair<Var, Var>, Const>,
                    val children: Map<Map<Var, Const>, Tree>) : Tree()
    data class Leaf(val payoff: Map<Var, Num>) : Tree()
}

class Extensive(private val name: String, private val desc: String, private val players: List<String>, private val game: Tree) {
    constructor(prog: ExpProgram) :
        this(prog.name, prog.desc, findPlayers(prog.game), fromExp(prog.game, mapOf(), mapOf()))

    fun toEfg(): String =
        (listOf("EFG 2 R ${q(name)} ${stringList(players)}", q(desc), "")
                + ExtensivePrinter().toEfg(game, players)).joinToString("\n")

    override fun toString(): String = game.toString()

}

fun fromExp(exp: Ext, g: Map<Var, Const>, h: Map<Pair<Var, Var>, Const>) : Tree = when (exp) {
    is Ext.BindSingle -> {
        when (exp.q.kind) {
            Kind.JOIN -> fromExp(exp.exp, g + Pair(exp.q.role, Address(maxAddress(g.values) + 1)), h)
            Kind.YIELD -> Tree.Node(owner = exp.q.role.name, children = buildChildren(exp, g, h), h = h)
            Kind.REVEAL -> fromExp(exp.exp, g, revealHidden(h, exp.q))
            Kind.MANY -> TODO()
        }
    }
    is Ext.Bind -> {
        val e = if (exp.qs.size == 1) {
            Ext.BindSingle(exp.qs.first(), exp.exp)
        } else {
            val reveals = exp.qs.fold(exp.exp) { acc, q -> Ext.BindSingle(q.copy(kind=Kind.REVEAL), acc) }
            val hides = exp.qs.fold(reveals) { acc, q -> Ext.BindSingle(hide(q), acc) }
            hides
        }
        fromExp(e, g, h)
    }
    is Ext.Value -> Tree.Leaf( (eval(exp.exp, g, h) as Q.PayoffConst).ts )
}

private fun hide(q: Query) =
    q.copy(params = q.params.map { it.copy(type = TypeExp.Hidden(it.type)) }, where = Bool(true))

fun findPlayers(exp: Ext): List<String> = when (exp) {
    is Ext.Bind -> exp.qs.filter { it.kind == Kind.JOIN } .map { it.role.name } + findPlayers(exp.exp)
    is Ext.BindSingle -> (if (exp.q.kind == Kind.JOIN) listOf(exp.q.role.name) else listOf()) + findPlayers(exp.exp)
    is Ext.Value -> listOf()
}

private fun revealHidden(h: Map<Pair<Var, Var>, Const>, q: Query) =
    h.mapValues { (rv, k) ->
        if (k is Hidden && rv.first == q.role
                && q.params.map{it.name.name}.contains(rv.second.name)) k.value else k
    }

private fun eraseHidden(h: Map<Pair<Var, Var>, Const>, role: Var) =
    h.mapValues { (rv, k) ->
        if (k is Hidden && rv.first != role) Hidden(UNDEFINED) else k
    }

private fun updateHeap(h: Map<Pair<Var, Var>, Const>, exp: Ext.BindSingle, g: Map<Var, Const>, newEnv: Map<Var, Const>) : Map<Pair<Var, Var>, Const> {
    val mh = h.toMutableMap()
    mh.putAll(newEnv.map{ (v, k) -> Pair(Pair(exp.q.role, v), k)})
    return mh.toMap()
}

private fun buildChildren(exp: Ext.BindSingle, g: Map<Var, Const>, h: Map<Pair<Var, Var>, Const>): Map<Map<Var, Const>, Tree> =
    vals(exp.q.params).filter { newEnv ->
        eval(exp.q.where, g, updateHeap(h, exp, g, newEnv)) == Bool(true)
    }.map { newEnv ->
        Pair(newEnv, fromExp(exp.exp, g, updateHeap(h, exp, g, newEnv)))
    }.toMap()

private fun maxAddress(values: Iterable<Const>) : Int =
        values.map { (it as? Address)?.n ?: 0 }.max() ?: 0


fun vals(params: List<VarDec>) : List<Map<Var, Const>> =
        params.map { d -> Pair(d.name, enumerateValues(d.type)) }.toMap().product()

fun eval(exp: Exp, g: Map<Var, Const>, h: Map<Pair<Var, Var>, Const>) : Const {
    fun eval(exp: Exp) = eval(exp, g, h)
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
        is Var -> g.getValue(exp)
        is Member -> h.getValue( Pair(exp.target, Var(exp.field)) )
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
        is Q.Let -> eval(exp.value, g + Pair(exp.dec.name, eval(exp.dec.name)), h)
        is Q.Payoff -> Q.PayoffConst(exp.ts.map { (k, v) -> Pair(k, eval(v) as Num)} .toMap())
        is Q.PayoffConst -> exp
    }
}

private fun enumerateValues(t: TypeExp): List<Const> = when(t) {
    is TypeExp.Opt -> enumerateValues(t.type) + UNDEFINED
    is TypeExp.Subset -> t.values.toList()
    TypeExp.BOOL -> listOf(Bool(true), Bool(false))
    is TypeExp.Hidden -> enumerateValues(t.type).map{ hide(it) }
    else -> throw AssertionError("cannot enumerate $t")
}

private fun hide(v: Const) : Const = when (v) {
    UNDEFINED -> UNDEFINED
    else -> Hidden(v)
}

class ExtensivePrinter {
    private var outcomeNumber: Int = 0

    fun toEfg(t: Tree, roleOrder: List<String>): List<String> = when (t) {
        is Tree.Node -> {
            val (values, children) = t.children.entries.map { it.toPair() }.unzip()
            val nodeName = ""
            val owner: Int = roleOrder.indexOf(t.owner) + 1
            // TODO: remove last assignment
            val infoset: Int = UniqueHash.of(eraseHidden(t.h, Var(t.owner))) // FIX: do we consider current choice???
            val infosetName = ""
            val actionNamesForInfoset: String = stringList(values.map { env -> env.values.map{valueToName(it)}.joinToString("&") })
            val outcome = 0
            val nameOfOutcome = ""
            val payoffs = 0
            listOf("p ${q(nodeName)} $owner $infoset ${q(infosetName)} $actionNamesForInfoset $payoffs") + children.flatMap { toEfg(it, roleOrder) }
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

private fun montyHall(): ExpProgram {
    val doors = TypeExp.Subset(setOf(Num(0), Num(1), Num(2)))
    val exp = join("host",
        exp = join("guest",
        exp = yield("host", VarDec(Var("car"), doors), hidden = true,
        exp = yield("guest", VarDec(Var("door"), doors),
        exp = yield("host", VarDec(Var("goat"), doors),
                 UnOp("!", BinOp("==", Member(Var("host"), "goat"), Member(Var("guest"), "door"))),
        exp = yield("guest", VarDec(Var("switch"), TypeExp.BOOL),
        exp = reveal("host", VarDec(Var("car"), doors),
        exp = Ext.Value(Q.Payoff(mapOf(
                Pair(Var("host"), Num(0)),
                Pair(Var("guest"), Cond(
                        UnOp("!", BinOp("==",
                                BinOp("==", Member(Var("host"), "car"), Member(Var("guest"), "door")),
                                Member(Var("guest"), "switch")
                        )), Num(10), Num(-10)
                ))
        ))
        ))))))))
    return ExpProgram("MontyHall", "Monty Hall Game", listOf(), exp)
}

fun join(role: String, exp: Ext) =
        Ext.Bind(listOf(Query(Kind.JOIN, Var(role))), exp)

fun yield(role: String, v: VarDec, where: Exp = Bool(true), exp: Ext, hidden: Boolean = false) : Ext {
    val vh = if (hidden) v.copy(type=TypeExp.Hidden(v.type)) else v
    return Ext.Bind(listOf(Query(Kind.YIELD, Var(role), listOf(vh), where)), exp)
}

fun reveal(role: String, v: VarDec, exp: Ext) =
        Ext.Bind(listOf(Query(Kind.REVEAL, Var(role), listOf(v))), exp)

private fun oddsEvens(): ExpProgram {
    val exp = Ext.Bind(listOf(
            Query(Kind.JOIN, Var("Odd" )),
            Query(Kind.JOIN, Var("Even"))
        ),
        exp = Ext.Bind(listOf(
            Query(Kind.YIELD, Var("Odd" ), listOf(VarDec(Var("c"), TypeExp.BOOL))),
            Query(Kind.YIELD, Var("Even"), listOf(VarDec(Var("c"), TypeExp.BOOL)))
        ),
        exp = Ext.Value(
            Cond(BinOp("==", Member(Var("Odd"), "c"), Member(Var("Even"), "c")),
                Q.Payoff(mapOf(
                    Pair(Var("Odd"), Num(10)),
                    Pair(Var("Even"), Num(-10))
                )),
                Q.Payoff(mapOf(
                    Pair(Var("Odd"), Num(-10)),
                    Pair(Var("Even"), Num(10))
                ))
            )
        )
    ))
    return ExpProgram("OddsEvens", "Simultaneous Game", listOf(), exp)
}



fun main(args: Array<String>) {
    val m = oddsEvens()
    println(m)
    val e = Extensive(m)
    println(e)
    println(e.toEfg())
}
