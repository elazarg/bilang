package bilang
import bilang.Exp.*

sealed class Tree {
    data class Node(val owner: String, val infset: Int, val children: Map<Map<Var, Const>, Tree>) : Tree()
    data class Leaf(val payoff: Map<Var, Num>) : Tree()
}

fun fromExp(exp: Exp, g: Map<Var, Const>, h: Map<Address, Map<Var, Const>>, values: (TypeExp) -> List<Const>) : Tree =
    when (exp) {
        is Q.Y -> {
            val children = vals(values, exp.p.params).filter {
                newEnv -> eval(exp.p.where, g, updateHeap(h, exp, g, newEnv)) == Bool(true)
            }.map {
                newEnv -> Pair(newEnv, fromExp(exp.exp, g + newEnv, h, values))
            }.toMap()
            Tree.Node(owner=exp.p.role.name, infset=1, children=children)
        }
        else -> Tree.Leaf( (eval(exp, g, h = mapOf()) as Q.PayoffConst).ts )
    }

private fun updateHeap(h: Map<Address, Map<Var, Const>>, exp: Q.Y, g: Map<Var, Const>, newEnv: Map<Var, Const>) =
        h.map { m -> Pair(m.key, if (m.key == eval(exp.p.role, g, h)) m.value + newEnv else m.value) }.toMap()

fun vals(values: (TypeExp) -> List<Const>, params: List<VarDec>) : List<Map<Var, Const>> =
        params.map { d -> Pair(d.name, values(d.type)) }.toMap().product()

fun eval(exp: Exp, g: Map<Var, Const>, h: Map<Address, Map<Var, Const>>) : Const {
    fun eval(exp: Exp) = eval(exp, g, h)
    return when (exp) {
        is Exp.Q.Y -> throw AssertionError()
        is Exp.Call -> TODO()
        is Exp.UnOp -> when (exp.op) {
            "-" -> Num(-(eval(exp.operand) as Num).n)
            "!" -> Bool(!(eval(exp.operand) as Bool).truth)
            else -> throw AssertionError()
        }
        is Exp.BinOp -> {
            val (left, right) = Pair(eval(exp.left), eval(exp.right))
            when {
                left is Num && right is Num -> when(exp.op) {
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
                else -> throw AssertionError()
            }
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
