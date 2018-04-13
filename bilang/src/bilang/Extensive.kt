package bilang
import bilang.Exp.*

sealed class Tree {
    data class Node(val owner: String, val infset: Int, val children: Map<Map<Var, Const>, Tree>) : Tree()
    data class Leaf(val payoff: Map<Var, Num>) : Tree()
}

fun fromExp(exp: Exp, g: Map<Var, Const>, h: Map<Address, Map<Var, Const>>,
            values: (TypeExp) -> List<Const>) : Tree =
    when {
        exp is Q.Y && exp.action == GameAction.YIELD -> {
            assert(exp.action == GameAction.YIELD)
            val children = vals(values, exp.p.params).filter {
                newEnv -> eval(exp.p.where, g, updateHeap(h, exp, g, newEnv)) == Bool(true)
            }.map {
                newEnv -> Pair(newEnv, fromExp(exp.exp, g, updateHeap(h, exp, g, newEnv), values))
            }.toMap()
            Tree.Node(owner=exp.p.role.name, infset=1, children=children)
        }
        exp is Q.Y && exp.action == GameAction.JOIN -> {
            fromExp(exp.exp, g + Pair(exp.p.role, Address(maxInt(g.values) + 1)), h, values)
        }
        exp is Exp.Q.Reveal -> throw AssertionError()
        else -> Tree.Leaf( (eval(exp, g, h) as Q.PayoffConst).ts )
    }

private fun maxInt(values: Iterable<Const>) : Int =
        values.map { (it as? Address)?.n ?: 0 }.max() ?: 0

private fun updateHeap(h: Map<Address, Map<Var, Const>>, exp: Q.Y, g: Map<Var, Const>, newEnv: Map<Var, Const>) =
        h.map { m -> Pair(m.key, if (m.key == eval(exp.p.role, g, h)) m.value + newEnv else m.value) }.toMap()

fun vals(values: (TypeExp) -> List<Const>, params: List<VarDec>) : List<Map<Var, Const>> =
        params.map { d -> Pair(d.name, values(d.type)) }.toMap().product()

fun eval(exp: Exp, g: Map<Var, Const>, h: Map<Address, Map<Var, Const>>) : Const {
    fun eval(exp: Exp) = eval(exp, g, h)
    return when (exp) {
        is Exp.Q.Y -> throw AssertionError()
        is Exp.Q.Reveal -> throw AssertionError()
        is Exp.Call -> TODO()
        is Exp.UnOp -> when (exp.op) {
            "-" -> Num(-(eval(exp.operand) as Num).n)
            "!" -> Bool(!(eval(exp.operand) as Bool).truth)
            else -> throw AssertionError()
        }
        is Exp.BinOp -> {
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
        is Exp.Var -> g.getValue(exp)
        is Exp.Member -> h.getValue(eval(exp.target) as Address).getValue(Var(exp.field))
        is Exp.Cond -> {
            val cond = eval(exp.cond)
            when (cond) {
                is Bool -> if (cond.truth) eval(exp.ifTrue) else eval(exp.ifFalse)
                else -> throw AssertionError()
            }
        }
        UNDEFINED -> UNDEFINED
        is Exp.Address -> exp
        is Exp.Num -> exp
        is Exp.Bool -> exp
        is Exp.Q.Let -> eval(exp.value, g + Pair(exp.dec.name, eval(exp.dec.name)), h)
        is Exp.Q.Payoff -> Exp.Q.PayoffConst(exp.ts.map { (k, v) -> Pair(k, eval(v) as Num)} .toMap())
        is Exp.Q.PayoffConst -> exp
    }
}
// TODO: add "undefined" as value
private fun enumerateValues(t: TypeExp): List<Const> = when(t) {
    is TypeExp.Subset -> t.values.toList()
    TypeExp.BOOL -> listOf(Bool(true), Bool(false))
    else -> throw AssertionError()
}

fun main(args: Array<String>) {
    val doors = TypeExp.Subset(setOf(Num(0), Num(1), Num(2)))
    val program =
                Q.Y(GameAction.JOIN,  Packet(Var("host"),  listOf(), Bool(true)),
            exp=Q.Y(GameAction.JOIN,  Packet(Var("guest"), listOf(), Bool(true)),
            exp=Q.Y(GameAction.YIELD, Packet(Var("host"),  listOf(VarDec(Var("car"),  doors)), Bool(true)), hidden=true,
            exp=Q.Y(GameAction.YIELD, Packet(Var("guest"), listOf(VarDec(Var("door"), doors)), Bool(true)),
            exp=Q.Y(GameAction.YIELD, Packet(Var("host"),  listOf(VarDec(Var("goat"), doors)),
                    UnOp("!", BinOp("==", Member(Var("host"), "goat"), Member(Var("guest"), "door")) )),
            exp=Q.Y(GameAction.YIELD, Packet(Var("guest"),  listOf(VarDec(Var("switch"), TypeExp.BOOL)), Bool(true)),
            //exp=Q.Reveal(Var("car"),
            exp=Q.Payoff(mapOf(
                    Pair(Var("host"), Num(0)),
                    Pair(Var("guest"), Cond(
                            UnOp("!", BinOp("==",
                                    BinOp("==", Member(Var("host"), "car"), Member(Var("guest"), "door")),
                                    Member(Var("guest"), "switch")
                            )), Num(10), Num(-10)
                    )
            )))
    ))))))//)
    val res = fromExp(program, g=mapOf(), h=mapOf(Address(1) to mapOf(), Address(2) to mapOf()), values = { enumerateValues(it) })
    println(res)
}

