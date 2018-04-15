package bilang
import bilang.Exp.*

sealed class Tree {
    data class Node(val owner: String, val h: Map<Var, Map<Var, Const>>,
                    val children: Map<Map<Var, Const>, Tree>) : Tree()
    data class Leaf(val payoff: Map<Var, Num>) : Tree()
}

fun fromExp(exp: Exp, g: Map<Var, Const>, h: Map<Var, Map<Var, Const>>,
            values: (TypeExp) -> List<Const>) : Tree =
        when (exp) {
            is Ext.Yield -> {
                val children = buildChildren(exp, g, h, values)
                Tree.Node(owner=exp.p.role.name, children=children, h=h)
            }
            is Ext.Join -> {
                fromExp(exp.exp, g + Pair(exp.p.role, Address(maxInt(g.values) + 1)), h, values)
            }
            is Ext.Reveal -> {
                val revealed = h.map { (r, b) ->
                    Pair(r, b.map { (v, k) -> Pair(v, if (r == exp.v.target && v.name == exp.v.field && k is Hidden) k.value else k) }.toMap())
                }.toMap()
                fromExp(exp.exp, g, revealed, values)
            }
            is Ext.Parallel<*> -> TODO()
            else -> Tree.Leaf( (eval(exp, g, h) as Q.PayoffConst).ts )
        }

private fun buildChildren(exp: Ext.Yield, g: Map<Var, Const>, h: Map<Var, Map<Var, Const>>,
                          values: (TypeExp) -> List<Const>): Map<Map<Var, Const>, Tree> =
    vals(values, exp.p.params).filter { newEnv ->
        eval(exp.p.where, g, updateHeap(h, exp, g, newEnv)) == Bool(true)
    }.map { newEnv ->
        Pair(newEnv, fromExp(exp.exp, g, updateHeap(h, exp, g, newEnv), values))
    }.toMap()

private fun maxInt(values: Iterable<Const>) : Int =
        values.map { (it as? Address)?.n ?: 0 }.max() ?: 0

private fun updateHeap(h: Map<Var, Map<Var, Const>>, exp: Ext.Yield, g: Map<Var, Const>, newEnv: Map<Var, Const>) =
        h.map { m -> Pair(m.key, if (g.getValue(m.key) == eval(exp.p.role, g, h)) m.value + newEnv else m.value) }.toMap()

fun vals(values: (TypeExp) -> List<Const>, params: List<VarDec>) : List<Map<Var, Const>> =
        params.map { d -> Pair(d.name, values(d.type)) }.toMap().product()

fun eval(exp: Exp, g: Map<Var, Const>, h: Map<Var, Map<Var, Const>>) : Const {
    fun eval(exp: Exp) = eval(exp, g, h)
    return when (exp) {
        is Ext -> throw AssertionError()
        is Call -> TODO()
        is UnOp -> when (exp.op) {
            "-" -> Num(-(eval(exp.operand) as Num).n)
            "!" -> Bool(!(eval(exp.operand) as Bool).truth)
            else -> throw AssertionError()
        }
        is BinOp -> {
            val (left, right) = Pair(eval(exp.left), eval(exp.right))
            val res: Const = when {
                left is Num && right is Num -> when (exp.op) {
                    "+" -> Num(left.n + right.n)
                    "-" -> Num(left.n - right.n)
                    "*" -> Num(left.n * right.n)
                    "/" -> Num(left.n / right.n)
                    "==" -> Bool(left.n == right.n)
                    else -> throw AssertionError()
                }
                left is Bool && right is Bool -> when (exp.op) {
                    "&&" -> Bool(left.truth && right.truth)
                    "||" -> Bool(left.truth || right.truth)
                    "==" -> Bool(left.truth == right.truth)
                    else -> throw AssertionError()
                }
                else -> throw AssertionError()
            }
            res
        }
        is Var -> g.getValue(exp)
        is Member -> h.getValue(exp.target).getValue(Var(exp.field))
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
        is Q.Payoff -> Exp.Q.PayoffConst(exp.ts.map { (k, v) -> Pair(k, eval(v) as Num)} .toMap())
        is Q.PayoffConst -> exp
    }
}

private fun enumerateValues(t: TypeExp): List<Const> = when(t) {
    is TypeExp.Subset -> t.values.toList() // + UNDEFINED
    TypeExp.BOOL -> listOf(Bool(true), Bool(false)) // + UNDEFINED
    is TypeExp.Hidden -> enumerateValues(t.type).map{Hidden(it)}
    else -> throw AssertionError()
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

    private fun eraseHidden(h: Map<Exp.Var, Map<Exp.Var, Exp.Const>>, role: Exp.Var): Map<Exp.Var, Map<Exp.Var, Exp.Const>> {
        return h.map {
            (r, f) -> Pair(r, f.map {
                (v, k) -> Pair(v, if (k is Hidden && r != role) Hidden(UNDEFINED) else k)
            }.toMap())
        }.toMap()
    }

    private fun valueToName(v: Const): String = when (v) {
        is Bool -> v.truth.toString()
        is Num -> v.n.toString()
        is Hidden -> "Hidden(${valueToName(v.value)}"
        UNDEFINED -> "None"
        else -> throw Exception(v.toString())
    }
}

private fun q(name: String) = '"' + name + '"'

private fun stringList(ss: Iterable<String>) = ss.joinToString(" ", "{ ", " }") { q(it) }

fun main(args: Array<String>) {
    val doors = TypeExp.Subset(setOf(Num(0), Num(1), Num(2)))
    val exp=Ext.Join(Packet(Var("host"),  listOf(), Bool(true)),
        exp=Ext.Join(Packet(Var("guest"), listOf(), Bool(true)),
        exp=Ext.Yield(Packet(Var("host"),  listOf(VarDec(Var("car"),  TypeExp.Hidden(doors))), Bool(true)), hidden=true,
        exp=Ext.Yield(Packet(Var("guest"), listOf(VarDec(Var("door"), doors)), Bool(true)),
        exp=Ext.Yield(Packet(Var("host"),  listOf(VarDec(Var("goat"), doors)),
                    UnOp("!", BinOp("==", Member(Var("host"), "goat"), Member(Var("guest"), "door")) )),
        exp=Ext.Yield(Packet(Var("guest"),  listOf(VarDec(Var("switch"), TypeExp.BOOL)), Bool(true)),
        exp=Ext.Reveal(Member(Var("host"), "car"),
        exp=Q.Payoff(mapOf(
                Pair(Var("host"), Num(0)),
                Pair(Var("guest"), Cond(
                        UnOp("!", BinOp("==",
                                BinOp("==", Member(Var("host"), "car"), Member(Var("guest"), "door")),
                                Member(Var("guest"), "switch")
                        )), Num(10), Num(-10)
                ))
            ))
    )))))))
    val res = fromExp(exp, g=mapOf(), h=mapOf(Var("host") to mapOf(), Var("guest") to mapOf()), values = { enumerateValues(it) })
    println(res)
    val header = listOf(
            "EFG 2 R ${q("MontyHall")} ${stringList(listOf("host", "guest"))}",
            q("Monty Hall Game"),
            ""
    )
    println((header + ExtensivePrinter().toEfg(res, listOf("host", "guest"))).joinToString("\n"))
}
