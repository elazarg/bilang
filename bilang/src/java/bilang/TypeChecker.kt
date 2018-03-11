package bilang

import bilang.TypeExp.*


/*
class Node(val b: List<Stmt>, nextList: List<Node>)

fun toCfg(b: Stmt.Block) : Node {


}

fun toSSA(p: Program) : Program {

}
*/

data class IncompatibleTypeError(val s: String) : Exception()

class Checker(_env: Map<Exp.Var, TypeExp>, private val typeMap: Map<String, TypeExp>) {
    val env = _env.toMutableMap()

    private val ROLE = TypeId("role")
    companion object {
        fun typeCheck(program: Program) {
            Checker(
                    mapOf(
                        Pair(Exp.Var("true"), BOOL),
                        Pair(Exp.Var("false"), BOOL)),
                    mapOf(
                        Pair("bool", BOOL),
                        Pair("role", TypeExp.ROLE),
                        Pair("int", INT)
                    )
            ).typeCheck(program.block)
        }
    }

    private fun typeCheck(block: Stmt.Block) {
        fun check(expected: TypeExp, exp: Exp) = checkOp(expected, type(exp))


        fun checkPackets(packets: List<Packet>): Map<Packet, Map<Exp.Var, TypeExp>> {
            val newEnv = packets.map { p -> Pair(p, p.params.map { d -> Pair(d.name, d.type) }.toMap()) }.toMap()
            for (p in packets)
                checkOp(BOOL, Checker(env + newEnv.getValue(p), typeMap).type(p.where))
            return newEnv
        }

        for (stmt in block.stmts) {
            when (stmt) {
                is Stmt.Def.VarDef -> {
                    check(stmt.dec.type, stmt.init)
                    env[stmt.dec.name] = stmt.dec.type
                }
                is Stmt.Def.YieldDef -> {
                    for (p in stmt.packets) check(ROLE, p.role)
                    val newEnv = checkPackets(stmt.packets)
                    for (k in newEnv.values)
                        env.plusAssign(k)
                }
                is Stmt.Def.JoinDef -> {
                    val newEnv = checkPackets(stmt.packets)
                    for (k in newEnv.values)
                        env.plusAssign(k)
                    for (p in stmt.packets)
                        env[p.role] = ROLE
                }
                is Stmt.Def.JoinManyDef -> env[stmt.role] = ROLESET
                is Stmt.Block -> Checker(env, typeMap).typeCheck(stmt)
                is Stmt.Assign -> check(env.getValue(stmt.target), stmt.exp)
                is Stmt.Reveal -> { } //TODO()
                is Stmt.If -> {
                    check(BOOL, stmt.cond)
                    Checker(env, typeMap).typeCheck(stmt.ifTrue)
                    Checker(env, typeMap).typeCheck(stmt.ifFalse)
                }
                is Stmt.ForYield -> {
                    checkPackets(listOf(stmt.packet))
                    typeCheck(stmt.block)
                    check(ROLESET, stmt.from)
                    env[stmt.packet.role] = ROLE
                }
                is Stmt.Transfer -> {
                    check(INT, stmt.amount)
                    check(ROLE, stmt.from)
                    check(ROLE, stmt.to)
                }
            }
        }
    }

    private fun type(exp: Exp): TypeExp {
        return when (exp) {
            is Exp.Call -> when (exp.target.name) {
                "abs" -> {
                    checkOp(INT, exp.args.map { e -> type(e) }); INT
                }
                else -> throw IllegalArgumentException(exp.target.name)
            }
            is Exp.UnOp -> when (exp.op) {
                "-" -> {
                    checkOp(INT, type(exp.operand)); INT
                }
                "!" -> {
                    checkOp(BOOL, type(exp.operand)); BOOL
                }
                else -> throw IllegalArgumentException(exp.op)
            }
            is Exp.BinOp -> {
                val left = type(exp.left)
                val right = type(exp.right)
                when (exp.op) {
                    "+", "-", "*", "/"   -> { checkOp(INT, left, right); INT }
                    ">", ">=", "<", "<=" -> { checkOp(INT, left, right); BOOL }
                    "||", "&&" ->           { checkOp(BOOL, left, right); BOOL }
                    "==", "!=" -> {
                        require(compatible(left, right) || compatible(right, left), { "$left <> $right"})
                        BOOL
                    }
                    else -> throw IllegalArgumentException(exp.op)
                }
            }
            is Exp.Num -> INT
            is Exp.Address -> ADDRESS
            is Exp.Var -> env.getValue(exp)
            is Exp.Member -> {
                checkOp(ROLE, type(exp.target))
                INT // FIX
            }
            is Exp.Cond -> {
                checkOp(BOOL, type(exp.cond))
                join(type(exp.ifTrue), type(exp.ifFalse))
            }
            Exp.UNDEFINED -> UNIT
        }
    }

    private fun checkOp(expected: TypeExp, args: Collection<TypeExp>) = checkOp(expected, *args.toTypedArray())
    private fun checkOp(expected: TypeExp, vararg args: TypeExp) {
        for (arg in args)
            require(compatible(arg, expected))
    }

    private fun compatible(t1: TypeExp, t2: TypeExp): Boolean {
        return t1 == t2
            || join(t1, t2) == t2
            || join(t1, t2) == t1 && t1 is Range && t2 is Subset && t2.values.size == t1.max.n - t1.min.n
    }

    private fun join(t1: TypeExp, t2: TypeExp): TypeExp = when {
        t1 === UNIT -> t2
        t2 === UNIT -> t1

        t1 == t2 -> t1
        t1 is TypeId -> {
            require(typeMap.containsKey(t1.name), { "$t1 not in type map" })
            join(typeMap.getValue(t1.name), t2)
        }
        t2 is TypeId -> {
            require(typeMap.containsKey(t2.name), { "$t2 not in type map" })
            join(t1, typeMap.getValue(t2.name))
        }

        t1 === ROLE && t2 === ROLE -> ROLE
        t1 === ROLESET && t2 === ROLESET -> ROLESET
        t1 === ADDRESS && t2 === ADDRESS -> ADDRESS
        t1 === BOOL && t2 === BOOL -> BOOL
        t1 === INT && t2 is IntClass -> INT
        t1 is IntClass && t2 === INT -> INT
        t1 is Subset && t2 is Subset -> Subset(t1.values union t2.values)
        t1 is Range && t2 is Range -> Range(Exp.Num(minOf(t1.min.n, t2.min.n)), Exp.Num(maxOf(t1.max.n, t2.max.n)))
        t1 is Subset && t2 is Range -> join(t2, t2)
        t1 is Range && t2 is Subset -> {
            val values = t2.values.map { x -> x.n }
            val min = minOf(t1.min.n, values.min()!!)
            val max = minOf(t1.max.n, values.max()!!)
            if (t2.values.size == max - min) t2
            else Range(Exp.Num(min), Exp.Num(max))
        }
        else -> throw IncompatibleTypeError("$t1 !< $t2")
    }

}