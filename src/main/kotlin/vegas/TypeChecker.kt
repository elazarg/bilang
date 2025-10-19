package vegas

import vegas.TypeExp.*

internal class StaticError(reason: String, val node: Ast) : RuntimeException(reason) {
    fun span(): Span? = SourceLoc.get(node)
}

// Short helpers to keep call sites terse
internal fun pt(t: TypeExp): String = Pretty.type(t)
internal fun pvd(vd: VarDec): String = "${vd.first}: ${pt(vd.second)}"

internal object Pretty {
    fun type(t: TypeExp): String = when (t) {
        INT -> "int"
        BOOL -> "bool"
        ROLE -> "role"
        ROLESET -> "roleset"
        ADDRESS -> "address"
        EMPTY -> "∅"
        is TypeId -> t.name
        is Hidden -> "hidden ${wrapIfComplex(t.type)}"
        is Opt -> "opt ${wrapIfComplex(t.type)}"
        is Subset -> "{${t.values.joinToString(",") { it.n.toString() }}}"
        is Range -> "{${t.min.n}..${t.max.n}}"
    }

    private fun wrapIfComplex(t: TypeExp): String = when (t) {
        is TypeId, INT, BOOL, ROLE, ROLESET, ADDRESS -> type(t)
        else -> "(${type(t)})"
    }

    fun exp(e: Exp): String = when (e) {
        is Exp.Const.Num -> e.n.toString()
        is Exp.Const.Bool -> e.truth.toString()
        is Exp.Const.Address -> "@${e.n}"
        is Exp.Const.Hidden -> "hidden(${exp(e.value)})"
        Exp.Const.UNDEFINED -> "undefined"
        is Exp.Var -> e.name
        is Exp.Member -> "${e.target}.${e.field}"
        is Exp.UnOp -> "${e.op}${paren(exp(e.operand))}"
        is Exp.BinOp -> "(${exp(e.left)} ${e.op} ${exp(e.right)})"
        is Exp.Cond -> "${paren(exp(e.cond))} ? ${exp(e.ifTrue)} : ${exp(e.ifFalse)}"
        is Exp.Call -> "${e.target.name}(${e.args.joinToString(", ") { exp(it) }})"
        is Exp.Let -> "let! ${pvd(e.dec)} = ${exp(e.init)} in ${exp(e.exp)}"
    }

    private fun paren(s: String) = if (needsParen(s)) "($s)" else s
    private fun needsParen(s: String) = s.any { it == ' ' || it in charArrayOf('?', ':') }
}

fun requireStatic(b: Boolean, s: String, node: Ast) {
    if (!b) throw StaticError(s, node)
}

fun typeCheck(program: ExpProgram) {
    Checker(
        program.types + mapOf(
            Pair("bool", BOOL),
            Pair("role", ROLE),
            Pair("int", INT)
        )
    ).type(program.game)
}

private fun Env<TypeExp>.safeGetValue(role: String, name: String, node: Ast): TypeExp =
    try {
        getValue(role, name)
    } catch (_: NoSuchElementException) {
        throw StaticError("Member '$role.$name' is undefined or role '$role' is not in scope", node)
    }

private class Checker(private val typeMap: Map<String, TypeExp>, private val env: Env<TypeExp> = Env()) {

    private fun requireRole(q: Query) {
        try {
            requireStatic(env.getValue(q.role) == ROLE, "${q.role} is not a role", q)
        } catch (_: NoSuchElementException) {
            throw StaticError("Role '${q.role}' is undefined", q)
        }
    }

    fun stripHidden(t: TypeExp): TypeExp = when (t) {
        is Hidden -> stripHidden(t.type)
        else -> t
    }

    fun type(ext: Ext) {
        when (ext) {
            is Ext.Bind -> {
                val (ns, ms) = ext.qs.map { q ->
                    for (c in q.params) {
                        val t = stripHidden(c.type)
                        if (t is TypeId && !typeMap.containsKey(t.name)) {
                            throw StaticError("Unknown type '${t.name}'", t)
                        }
                    }
                    val m = q.params.associate { (k, v) -> Pair(q.role, k) to v }
                    when (ext.kind) {
                        Kind.JOIN, Kind.JOIN_CHANCE -> {
                            val n = mapOf(q.role to ROLE)
                            checkWhere(n, m, q)
                            Pair(n, m)
                        }

                        Kind.YIELD -> {
                            requireRole(q)
                            val n = mapOf<String, TypeExp>()
                            checkWhere(n, m, q)
                            Pair(n, m)
                        }

                        Kind.REVEAL -> {
                            requireRole(q)
                            m.forEach { (rf, revealedType) ->
                                val (role, field) = rf
                                val existing = env.safeGetValue(role, field, q)
                                requireStatic(existing is Hidden, "Parameter '$role.$field' must be hidden", q)
                                val expected = (existing as Hidden).type
                                requireStatic(
                                    compatible(revealedType, expected) && compatible(expected, revealedType),
                                    "Reveal type mismatch for '$role.$field': expected ${pt(expected)}, got ${
                                        pt(
                                            revealedType
                                        )
                                    }", q
                                )
                            }
                            val n = emptyMap<String, TypeExp>()
                            checkWhere(n, m, q)
                            Pair(n, m)
                        }
                    }
                }.unzip()
                Checker(typeMap, env + ns.union() with ms.union()).type(ext.ext)
            }

            is Ext.BindSingle -> type(Ext.Bind(ext.kind, listOf(ext.q), ext.ext))

            is Ext.Value -> type(ext.exp)
        }
    }

    private fun checkWhere(n: Map<String, TypeExp>, m: Map<Pair<String, String>, TypeExp>, q: Query) {
        requireStatic(Checker(typeMap, env + n with m).type(q.where) == BOOL, "Where clause failed", q)
    }

    private fun type(outcome: Outcome) {
        when (outcome) {
            is Outcome.Cond -> {
                requireStatic(type(outcome.cond) == BOOL, "Outcome condition must be boolean", outcome)
                type(outcome.ifTrue)
                type(outcome.ifFalse)
            }

            is Outcome.Value -> {
                outcome.ts.forEach { (role, v) ->
                    try {
                        requireStatic(env.getValue(role) == ROLE, "$role is not a role", outcome)
                    } catch (_: NoSuchElementException) {
                        throw StaticError("Role '${role}' is undefined", outcome)
                    }
                    requireStatic(type(v) == INT, "Outcome value must be an int", v)
                }
            }

            is Outcome.Let -> {
                requireStatic(type(outcome.init) == outcome.dec.type, "Bad initialization of let ext", outcome.init)
                Checker(typeMap, env + outcome.dec).type(outcome.outcome)
            }
        }
    }

    private fun type(exp: Exp): TypeExp = when (exp) {
        is Exp.Call -> {
            val argTypes = exp.args.map { type(it) }
            when (exp.target.name) {
                "abs" -> {
                    checkOp(INT, argTypes)
                    INT
                }

                "alldiff" -> {
                    // require at least 2 args?
                    checkOp(INT, argTypes) // all args must be INT
                    BOOL
                }

                else -> throw IllegalArgumentException(exp.target.name)
            }
        }

        is Exp.UnOp -> {
            val operandType = type(exp.operand)
            when (exp.op) {
                "-" -> {
                    checkOp(INT, operandType); INT
                }

                "!" -> {
                    checkOp(BOOL, operandType); BOOL
                }

                "isUndefined", "isDefined" -> {
                    // We'll need flow-sensitivity to check this
                    // requireStatic(type(exp.operand) is Opt, "`isUndefined` arg must be `Opt`")
                    BOOL
                }

                else -> throw IllegalArgumentException(exp.op)
            }
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
                    requireStatic(
                        compatible(left, right) || compatible(right, left),
                        "${pt(left)} <> ${pt(right)} (1)", exp
                    )
                    BOOL
                }

                "<->", "<-!->" -> {
                    requireStatic(
                        compatible(left, BOOL) || compatible(right, BOOL),
                        "either ${pt(left)} or ${pt(right)} are incompatible with bool", exp
                    )
                    BOOL
                }

                else -> throw IllegalArgumentException(exp.op)
            }
        }

        is Exp.Const.Num -> INT
        is Exp.Const.Address -> ADDRESS
        is Exp.Const.Bool -> BOOL
        is Exp.Const.Hidden -> Hidden(type(exp.value as Exp))
        is Exp.Var -> try {
            env.getValue(exp.name)
        } catch (e: NoSuchElementException) {
            throw StaticError("Variable '${exp.name}' is undefined", exp)
        }
        is Exp.Member -> {
            try {
                val role = env.getValue(exp.target)
                requireStatic(role == ROLE, "${exp.target} is not a role", exp)
            } catch (_: NoSuchElementException) {
                throw StaticError("Role '${exp.target}' is undefined", exp)
            }
            env.safeGetValue(exp.target, exp.field, exp)
        }

        is Exp.Cond -> {
            checkOp(BOOL, type(exp.cond))
            join(type(exp.ifTrue), type(exp.ifFalse))
        }

        is Exp.Let -> {
            requireStatic(type(exp.init) == exp.dec.type, "Bad initialization of let exp", exp)
            Checker(typeMap, env + exp.dec).type(exp.exp)
        }

        Exp.Const.UNDEFINED -> throw AssertionError()
    }

    private fun checkOp(expected: TypeExp, args: Collection<TypeExp>) = checkOp(expected, *args.toTypedArray())
    private fun checkOp(expected: TypeExp, vararg args: TypeExp) {
        for (arg in args) {
            requireStatic(
                compatible(arg, expected),
                "Incompatible operator argument: Expected ${pt(expected)}, actual ${pt(arg)}", arg
            )
        }
    }

    // Assumes TypeId resolution (if any) already happened before this call.
    // Hidden wrappers are erased for the purpose of compatibility.
    private fun compatible(t1Raw: TypeExp, t2Raw: TypeExp): Boolean {
        // 1) Normalize away 'hidden'

        val t1 = stripHidden(t1Raw)
        val t2 = stripHidden(t2Raw)

        // 2) Trivial equality
        if (t1 == t2) return true

        // 3) If their join collapses to one side, we consider them compatible
        val j = join(t1, t2)
        if (j == t1 || j == t2) return true

        // 4) Range ↔ Subset: a subset is compatible with a range
        //    if *all* its elements lie inside the inclusive range.
        fun subsetWithinRange(sub: Subset, rng: Range): Boolean {
            val lo = rng.min.n
            val hi = rng.max.n
            return sub.values.all { v ->
                v.n in lo..hi
            }
        }

        return when {
            t1 is Range && t2 is Subset -> subsetWithinRange(t2, t1)
            t2 is Range && t1 is Subset -> subsetWithinRange(t1, t2)
            else -> false
        }
    }

    private fun join(t1: TypeExp, t2: TypeExp): TypeExp = when {
        t1 is Opt && t2 is Opt -> Opt(join(t1.type, t2.type))
        t1 is Opt -> Opt(join(t1.type, t2))
        t2 is Opt -> Opt(join(t1, t2.type))
        t1 == t2 -> t1
        t1 is TypeId -> {
            requireStatic(typeMap.containsKey(t1.name), "${pt(t1)} not in type map", t1)
            join(typeMap.getValue(t1.name), t2)
        }

        t2 is TypeId -> {
            requireStatic(typeMap.containsKey(t2.name), "${pt(t2)} not in type map", t2)
            join(t1, typeMap.getValue(t2.name))
        }

        t1 === TypeId("role") && t2 === TypeId("role") -> TypeId("role")
        t1 === ROLESET && t2 === ROLESET -> ROLESET
        t1 === ADDRESS && t2 === ADDRESS -> ADDRESS
        t1 === BOOL && t2 === BOOL -> BOOL
        t1 === INT && t2 is IntClass -> INT
        t1 === EMPTY || t2 === EMPTY -> EMPTY // TODO: is it not meet?
        t1 is IntClass && t2 === INT -> INT
        t1 is Subset && t2 is Subset -> Subset(t1.values union t2.values)
        t1 is Range && t2 is Range -> Range(
            Exp.Const.Num(minOf(t1.min.n, t2.min.n)),
            Exp.Const.Num(maxOf(t1.max.n, t2.max.n))
        )

        t1 is Subset && t2 is Range -> join(t2, t2)
        t1 is Range && t2 is Subset -> {
            val values = t2.values.map { it.n }
            val min = minOf(t1.min.n, values.minOrNull()!!)
            val max = minOf(t1.max.n, values.maxOrNull()!!)
            if (t2.values.size == max - min) t2
            else Range(Exp.Const.Num(min), Exp.Const.Num(max))
        }

        else -> EMPTY
    }

}

