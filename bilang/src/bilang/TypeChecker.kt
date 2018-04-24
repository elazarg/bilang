package bilang

import bilang.TypeExp.*

data class IncompatibleTypeError(val s: String) : Exception()


internal class StaticError(val line: Int, reason: String) : RuntimeException(reason)

class Checker(_env: Map<Exp.Var, TypeExp>, private val typeMap: Map<String, TypeExp>) {
    val env = _env.toMutableMap()

    private val ROLE = TypeId("role")

    companion object {
        fun typeCheck(program: ExpProgram) {
            Checker(
                    mapOf(
                            Pair(Exp.Var("true"), BOOL),
                            Pair(Exp.Var("false"), BOOL)),
                    mapOf(
                            Pair("bool", BOOL),
                            Pair("role", TypeExp.ROLE),
                            Pair("int", INT)
                    )
            ).type(program.game)
        }
    }
    private fun type(outcome: Outcome): Nothing = TODO()

    private fun type(ext: Ext) {
        when (ext) {
            is Ext.Bind -> TODO()
            is Ext.BindSingle -> TODO()
            is Ext.Value -> type(ext.exp)
        }
    }

    private fun type(exp: Exp): TypeExp = when (exp) {
        is Exp.Call -> when (exp.target.name) {
            "abs" -> {
                checkOp(INT, exp.args.map { type(it) }); INT
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
            "isUndefined" -> { require(type(exp.operand) is Opt); BOOL }
            else -> throw IllegalArgumentException(exp.op)
        }
        is Exp.BinOp -> {
            val left = type(exp.left)
            val right = type(exp.right)
            when (exp.op) {
                "+", "-", "*", "/" -> {
                    checkOp(INT, left, right)
                    INT
                }
                ">", ">=", "<", "<=" -> {
                    checkOp(INT, left, right)
                    BOOL
                }
                "||", "&&" -> {
                    checkOp(BOOL, left, right)
                    BOOL
                }
                "==", "!=" -> {
                    require(compatible(left, right) || compatible(right, left), { "$left <> $right" })
                    BOOL
                }
                "<->", "<-!->" -> {
                    require(compatible(left, BOOL) || compatible(right, BOOL), { "$left <> $right" })
                    BOOL
                }
                else -> throw IllegalArgumentException(exp.op)
            }
        }
        is Exp.Const.Num -> INT
        is Exp.Const.Address -> ADDRESS
        is Exp.Const.Bool -> BOOL
        is Exp.Const.Hidden -> TypeExp.Hidden(type(exp.value as Exp))
        is Exp.Var -> env.getValue(exp)
        is Exp.Member -> {
            checkOp(ROLE, type(Exp.Var(exp.target)))
            INT // FIX
        }
        is Exp.Cond -> {
            checkOp(BOOL, type(exp.cond))
            join(type(exp.ifTrue), type(exp.ifFalse))
        }

        is Exp.Let -> TODO()
        Exp.Const.UNDEFINED -> TODO() // We shouldn't really get here
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
        t1 is Opt && t2 is Opt -> Opt(join(t1.type, t2.type))
        t1 is Opt -> Opt(join(t1.type, t2))
        t2 is Opt -> Opt(join(t1, t2.type))
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
        t1 is Range && t2 is Range -> Range(Exp.Const.Num(minOf(t1.min.n, t2.min.n)), Exp.Const.Num(maxOf(t1.max.n, t2.max.n)))
        t1 is Subset && t2 is Range -> join(t2, t2)
        t1 is Range && t2 is Subset -> {
            val values = t2.values.map { it.n }
            val min = minOf(t1.min.n, values.min()!!)
            val max = minOf(t1.max.n, values.max()!!)
            if (t2.values.size == max - min) t2
            else Range(Exp.Const.Num(min), Exp.Const.Num(max))
        }
        else -> throw IncompatibleTypeError("$t1 !< $t2")
    }

}

