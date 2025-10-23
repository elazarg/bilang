package vegas.ir

import vegas.FieldRef
import vegas.RoleId
import vegas.frontend.Exp as AstExpr
import vegas.frontend.TypeExp as AstType
import vegas.frontend.*

/**
 * Compile AST to IR.
 *
 * Transformations:
 * - Flatten Ext tree into phases
 * - Group simultaneous queries (same Bind) into single phase
 * - Elaborate types: TypeId->resolved, Range->SetType, Hidden->visible flag
 * - Transform expressions: isDefined/isUndefined->IsDefined
 * - Desugar outcomes to payoff expressions
 */
fun compileToIR(ast: GameAst): GameIR {
    val typeEnv = ast.types
    val roles = findRoleIds(ast.game)

    val phases = collectPhases(ast.game, typeEnv)
    val payoffs = extractPayoffs(ast.game, typeEnv)

    return GameIR(
        name = ast.name,
        roles = roles,
        phases = phases,
        payoffs = payoffs
    )
}

// ========== Phase Collection ==========

private fun collectPhases(ext: Ext, typeEnv: Map<AstType.TypeId, AstType>): List<Phase> {
    return when (ext) {
        is Ext.Bind -> {
            // Multiple queries in same Bind -> same phase (simultaneous)
            val phase: Phase = ext.qs.associate { query ->
                query.role.id to lowerQuery(query, ext.kind, typeEnv)
            }
            listOf(phase) + collectPhases(ext.ext, typeEnv)
        }

        is Ext.BindSingle -> {
            // Single query -> single-entry phase
            val phase: Phase = mapOf(
                ext.q.role.id to lowerQuery(ext.q, ext.kind, typeEnv)
            )
            listOf(phase) + collectPhases(ext.ext, typeEnv)
        }

        is Ext.Value -> emptyList() // Terminal: no more phases
    }
}

private fun lowerQuery(query: Query, kind: Kind, typeEnv: Map<AstType.TypeId, AstType>): Signature {
    return Signature(
        join = when (kind) {
            Kind.JOIN -> Join(Expr.IntVal(query.deposit.n))
            Kind.JOIN_CHANCE -> Join(Expr.IntVal(query.deposit.n))
            else -> null
        },
        parameters = query.params.map { vardec ->
            Parameter(
                name = vardec.v.id,
                type = lowerType(vardec.type, typeEnv),
                visible = !isHiddenType(vardec.type)
            )
        },
        requires = Requirement(
            captures = collectCaptures(query.where),
            condition = lowerExpr(query.where, typeEnv)
        )
    )
}

// ========== Type Lowering ==========

private fun isHiddenType(type: AstType): Boolean = when (type) {
    is AstType.Hidden -> true
    else -> false
}

private fun lowerType(type: AstType, typeEnv: Map<AstType.TypeId, AstType>): Type {
    return when (type) {
        AstType.INT -> Type.IntType
        AstType.BOOL -> Type.BoolType
        AstType.ADDRESS -> Type.IntType // Address as int in IR
        AstType.EMPTY -> error("EMPTY type should not reach IR")

        is AstType.Hidden -> lowerType(type.type, typeEnv) // Strip hidden wrapper

        is AstType.TypeId -> {
            val resolved = typeEnv[type] ?: error("Unknown type: ${type.name}")
            lowerType(resolved, typeEnv)
        }

        is AstType.Subset -> Type.SetType(type.values.map { it.n }.toSet())

        is AstType.Range -> {
            val values = (type.min.n..type.max.n).toSet()
            Type.SetType(values)
        }

        is AstType.Opt -> lowerType(type.type, typeEnv) // Strip opt wrapper
    }
}

// ========== Capture Collection ==========

private fun collectCaptures(exp: AstExpr): Set<FieldRef> {
    val captures = mutableSetOf<FieldRef>()

    fun collect(e: AstExpr) {
        when (e) {
            is AstExpr.Field -> {
                captures.add(e.fieldRef)
            }

            is AstExpr.UnOp -> collect(e.operand)

            is AstExpr.BinOp -> {
                collect(e.left)
                collect(e.right)
            }

            is AstExpr.Cond -> {
                collect(e.cond)
                collect(e.ifTrue)
                collect(e.ifFalse)
            }

            is AstExpr.Call -> e.args.forEach { collect(it) }

            is AstExpr.Let -> {
                collect(e.init)
                collect(e.exp)
            }

            is AstExpr.Var, is AstExpr.Const -> { /* no captures */ }
        }
    }

    collect(exp)
    return captures
}

// ========== Expression Lowering ==========

private fun lowerExpr(exp: AstExpr, typeEnv: Map<AstType.TypeId, AstType>): Expr {
    return when (exp) {
        // Literals
        is AstExpr.Const.Num -> Expr.IntVal(exp.n)
        is AstExpr.Const.Bool -> Expr.BoolVal(exp.truth)
        is AstExpr.Const.Address -> Expr.IntVal(exp.n)
        is AstExpr.Const.Hidden -> lowerExpr(exp.value, typeEnv)
        AstExpr.Const.UNDEFINED -> error("UNDEFINED should not appear in IR")

        // Field references
        is AstExpr.Field -> Expr.Field(exp.fieldRef)

        // Variables (shouldn't appear in well-typed AST)
        is AstExpr.Var -> error("Free variable in expression: ${exp.id}")

        // Unary operators
        is AstExpr.UnOp -> when (exp.op) {
            "isDefined" -> {
                val member = exp.operand as? AstExpr.Field
                    ?: error("isDefined requires Field operand, got: ${exp.operand}")
                Expr.IsDefined(member.fieldRef)
            }

            "isUndefined" -> {
                val member = exp.operand as? AstExpr.Field
                    ?: error("isUndefined requires Field operand, got: ${exp.operand}")
                Expr.Not(Expr.IsDefined(member.fieldRef))
            }

            "!" -> Expr.Not(lowerExpr(exp.operand, typeEnv))
            "-" -> Expr.Neg(lowerExpr(exp.operand, typeEnv))

            else -> error("Unknown unary operator: ${exp.op}")
        }

        // Binary operators
        is AstExpr.BinOp -> {
            val l = lowerExpr(exp.left, typeEnv)
            val r = lowerExpr(exp.right, typeEnv)

            when (exp.op) {
                // Arithmetic
                "+" -> Expr.Add(l, r)
                "-" -> Expr.Sub(l, r)
                "*" -> Expr.Mul(l, r)
                "/" -> Expr.Div(l, r)

                // Comparison
                "==" -> Expr.Eq(l, r)
                "!=" -> Expr.Ne(l, r)
                "<" -> Expr.Lt(l, r)
                "<=" -> Expr.Le(l, r)
                ">" -> Expr.Gt(l, r)
                ">=" -> Expr.Ge(l, r)

                // Boolean
                "&&" -> Expr.And(l, r)
                "||" -> Expr.Or(l, r)

                // Special operators
                "<->" -> Expr.Eq(l, r)  // Biconditional (iff) -> equality
                "<-!->" -> Expr.Ne(l, r) // XOR -> not-equal

                else -> error("Unknown binary operator: ${exp.op}")
            }
        }

        // Conditional
        is AstExpr.Cond -> Expr.Ite(
            lowerExpr(exp.cond, typeEnv),
            lowerExpr(exp.ifTrue, typeEnv),
            lowerExpr(exp.ifFalse, typeEnv)
        )

        // Function calls
        is AstExpr.Call -> when (exp.target.id.name) {
            "alldiff" -> {
                // alldiff(a, b, c) -> (a != b) && (a != c) && (b != c)
                val args = exp.args.map { lowerExpr(it, typeEnv) }

                if (args.size < 2) {
                    Expr.BoolVal(true) // alldiff of 0 or 1 elements is trivially true
                } else {
                    val pairs = args.indices.flatMap { i ->
                        ((i + 1) until args.size).map { j ->
                            Expr.Ne(args[i], args[j])
                        }
                    }
                    pairs.reduce<Expr,Expr> { acc, ne -> Expr.And(acc, ne) }
                }
            }

            "abs" -> {
                // abs(x) -> x >= 0 ? x : -x
                val arg = lowerExpr(exp.args.single(), typeEnv)
                Expr.Ite(
                    Expr.Ge(arg, Expr.IntVal(0)),
                    arg,
                    Expr.Neg(arg)
                )
            }

            else -> error("Unknown function: ${exp.target.id.name}")
        }

        // Let expressions (desugar by substitution)
        is AstExpr.Let -> {
            // For simplicity: error for now
            // Full implementation would need alpha-renaming and substitution
            error("Let expressions not yet supported in IR lowering")
        }
    }
}

// ========== Payoff Extraction ==========

private fun extractPayoffs(ext: Ext, typeEnv: Map<AstType.TypeId, AstType>): Map<RoleId, Expr> {
    return when (ext) {
        is Ext.Bind -> extractPayoffs(ext.ext, typeEnv)
        is Ext.BindSingle -> extractPayoffs(ext.ext, typeEnv)
        is Ext.Value -> desugarOutcome(ext.outcome, typeEnv)
    }
}

private fun desugarOutcome(outcome: Outcome, typeEnv: Map<AstType.TypeId, AstType>): Map<RoleId, Expr> {
    return when (outcome) {
        // Base case: direct value mapping
        is Outcome.Value -> {
            outcome.ts.mapKeys { it.key.id }
                .mapValues { lowerExpr(it.value, typeEnv) }
        }

        // Conditional outcome
        is Outcome.Cond -> {
            val ifTrue = desugarOutcome(outcome.ifTrue, typeEnv)
            val ifFalse = desugarOutcome(outcome.ifFalse, typeEnv)
            val cond = lowerExpr(outcome.cond, typeEnv)

            // Merge: for each role, create ite expression
            val allRoles = ifTrue.keys + ifFalse.keys
            allRoles.associateWith { role ->
                val t = ifTrue[role] ?: Expr.IntVal(0) // Default to 0 if role not in branch
                val f = ifFalse[role] ?: Expr.IntVal(0)
                Expr.Ite(cond, t, f)
            }
        }

        // Let in outcome (desugar by substitution)
        is Outcome.Let -> {
            // For simplicity: error for now
            // Full implementation would substitute and recurse
            error("Let in outcomes not yet supported in IR lowering")
        }
    }
}
