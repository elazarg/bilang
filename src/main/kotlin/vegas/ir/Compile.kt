package vegas.ir

import vegas.frontend.*                 // AST: Ext, Query, Kind, TypeExp, Exp, Outcome, Role, ProgramAst

/**
 * Lower a parsed + (lightly) checked AST into the block-based IR.
 * One AST Bind/BindSingle → one IR Block (simultaneous moves, same pre-state).
 */
object AstToIr {

    fun lower(p: ProgramAst): ProgramIR {
        val roles: Set<Role> = collectRoles(p)
        val ctx = LowerCtx(p, roles)

        val blocks = mutableListOf<Block>()
        flattenExt(p.game) { bi, qs ->
            blocks += Block(
                id = BlockId("b$bi"),
                moves = qs.mapIndexed { qi, q -> lowerMove(ctx, bi, qi, q) }
            )
        }

        val payoffs: Map<Role, Expr> = lowerOutcome(ctx, p.game)

        return ProgramIR(
            name = p.name,
            roles = roles,
            blocks = blocks,
            payoffs = payoffs
        )
    }

    // ---------- Context & bookkeeping ----------

    private fun collectRoles(p: ProgramAst): Set<Role> =
        (p.types.keys.map { it.name } to Unit).let {
            // Prefer explicit roles in Bind JOINs; else fall back to every role seen in queries
            val rs = findRoles(p.game) // AST helper provided in your file
            rs.toSet()
        }

    // ---------- Flatten Ext into (block index, queries) ----------

    private inline fun flattenExt(ext: Ext, emit: (Int, List<Query>) -> Unit) {
        var cur: Ext = ext
        var blockIndex = 0
        while (true) {
            when (cur) {
                is Ext.Bind -> {
                    emit(blockIndex, cur.qs)
                    blockIndex++
                    cur = cur.ext
                }
                is Ext.BindSingle -> {
                    emit(blockIndex, listOf(cur.q))
                    blockIndex++
                    cur = cur.ext
                }
                is Ext.Value -> break
            }
        }
    }

    // ---------- Lower a single Query to an IR Move ----------

    private fun lowerMove(ctx: LowerCtx, bi: Int, qi: Int, q: Query): Move {
        val kind = when (q.role) {
            Role.Chance -> MoveKind.CHANCE
            else -> when (inferKind(q)) {
                Kind.JOIN -> MoveKind.JOIN
                Kind.YIELD -> MoveKind.SUBMIT
                Kind.REVEAL -> MoveKind.REVEAL
                Kind.JOIN_CHANCE -> MoveKind.CHANCE
            }
        }
        val mid = ctx.freshMoveId(bi, qi, inferKind(q), q.role)

        val params = q.params.map { vd ->
            Param(vd.v.name, lowerType(ctx, vd.type))
        }

// Register producers and types for future lookups
        params.forEach { p ->
            ctx.lastProducer[q.role to p.name] = mid
            ctx.fieldTypeByProducer[mid to p.name] = p.type
        }
        val guard = lowerExpToBool(ctx, q.where)

        return Move(
            id = mid,
            by = q.role,
            kind = kind,
            params = params,
            guard = guard
        )
    }

    // The AST distinguishes Kind at the Bind level; queries themselves carry role/params/where.
    // If you need the exact Bind kind, thread it in; otherwise we infer:
    private fun inferKind(q: Query): Kind =
    // Heuristic: REVEAL moves typically have Hidden-typed params to be opened now;
        // otherwise honor Chance role.
        when {
            q.role == Role.Chance -> Kind.JOIN_CHANCE
            q.params.any { it.type is TypeExp.Hidden } && q.where is Exp.Const.Bool && q.where.truth -> Kind.REVEAL
            else -> Kind.YIELD // default submit
        }

    // ---------- Lower Outcome (payoffs) ----------
    private fun lowerExpToBool(ctx: LowerCtx, e: Exp): Expr =
        lowerExp(ctx, Env(), e).asBool(ctx)

    private fun lowerOutcome(ctx: LowerCtx, ext: Ext): Map<Role, Expr> {
        // Find the trailing Ext.Value (outcome)
        tailrec fun lastOutcome(e: Ext): Outcome = when (e) {
            is Ext.Bind -> lastOutcome(e.ext)
            is Ext.BindSingle -> lastOutcome(e.ext)
            is Ext.Value -> e.outcome
        }
        val outcome = lastOutcome(ext)
        val env = Env() // expression environment for Let bindings inside Outcome

        fun lower(o: Outcome): Map<Role, Expr> = when (o) {
            is Outcome.Value -> {
                o.ts.mapKeys { (r, _) ->
                    require(ctx.roles.contains(r)) { "Payoff references unknown role '$r'" }
                    r
                }.mapValues { (_, exp) -> lowerExp(ctx, env, exp) }
            }
            is Outcome.Cond -> {
                val c = lowerExpToBool(ctx, o.cond)
                val t = lower(o.ifTrue)
                val e = lower(o.ifFalse)
                // Merge by role with ITE
                (t.keys + e.keys).associateWith { r ->
                    val tv = t[r] ?: Expr.IntLit(0)
                    val ev = e[r] ?: Expr.IntLit(0)
                    Expr.Ite(c, tv, ev)
                }
            }
            is Outcome.Let -> {
                val v = lowerExp(ctx, env, o.init)
                env.bind(o.dec.v.name, v)
                lower(o.outcome)
            }
        }

        return lower(outcome)
    }

    // ---------- Types ----------

    private fun lowerType(ctx: LowerCtx, t: TypeExp): Type = when (t) {
        TypeExp.INT -> Type.IntType
        TypeExp.BOOL -> Type.BoolType
        is TypeExp.Range -> Type.Range(t.min.n, t.max.n)
        is TypeExp.Subset -> Type.Subset(t.values.map { it.n }.toSet())
        is TypeExp.Hidden -> Type.Hidden(lowerType(ctx, t.type))
        is TypeExp.Opt -> Type.Opt(lowerType(ctx, t.type))
        is TypeExp.TypeId -> {
            val def = ctx.typeDefs[t.name]
                ?: error("Unknown type id '${t.name}'")
            lowerType(ctx, def)
        }
        TypeExp.ADDRESS -> error("ADDRESS not supported in IR lowering")
        TypeExp.EMPTY -> error("EMPTY type not supported in IR lowering")
    }

    // ---------- Expressions ----------

    private class Env {
        private val m = LinkedHashMap<String, Expr>()
        fun lookup(n: String): Expr? = m[n]
        fun bind(n: String, e: Expr) { m[n] = e }
        fun shadow(n: String, e: Expr, k: () -> Expr): Expr {
            val old = m[n]
            m[n] = e
            val res = k()
            if (old == null) m.remove(n) else m[n] = old
            return res
        }
    }
    /** Definedness predicates only make sense on fields (action.param).
     *  Accept Exp.Member(role, field) or anything that lowers to Expr.Field;
     *  fail fast on other expressions (literals, arithmetic, etc.).
     */
    private fun lowerFieldForDefPred(ctx: LowerCtx, env: Env, operand: Exp): Expr.Field {
        return when (operand) {
            is Exp.Member -> {
                val moveId = ctx.lastProducer[operand.target to operand.field.name]
                    ?: error("No prior producer for ${operand.target}.${operand.field} in isDefined/isUndefined")
                Expr.Field(moveId, operand.field.name)
            }
            else -> {
                val lowered = lowerExp(ctx, env, operand)
                lowered as? Expr.Field ?: error("isDefined/isUndefined expects a field reference, got: $lowered")
            }
        }
    }

    private fun lowerExp(ctx: LowerCtx, env: Env, e: Exp): Expr = when (e) {
        is Exp.Const.Num -> Expr.IntLit(e.n)
        is Exp.Const.Bool -> Expr.Bool(e.truth)
        is Exp.Const.UNDEFINED -> error("Bare UNDEFINED cannot appear as a value in IR")
        is Exp.Const.Address -> error("ADDRESS constant unsupported in IR")
        is Exp.Const.Hidden -> {
            // Hidden constants appear only as commit preimages in the AST; IR does not model them as values.
            when (e.value) {
                is Exp.Const.Num -> Expr.IntLit(e.value.n) // best-effort
                is Exp.Const.Bool -> Expr.Bool(e.value.truth)
                else -> error("Unsupported Hidden constant payload: ${e.value}")
            }
        }

        is Exp.Var -> env.lookup(e.name)
            ?: error("Unbound variable ${e.name} in expression")

        is Exp.Member -> {
            val moveId = ctx.lastProducer[e.target to e.field.name]
                ?: error("No prior producer for ${e.target}.${e.field}")
            Expr.Field(moveId, e.field.name)
        }

        is Exp.UnOp -> when (e.op) {
            "!" -> Expr.Not(lowerExp(ctx, env, e.operand).asBool(ctx))
            "-" -> Expr.Sub(Expr.IntLit(0), lowerExp(ctx, env, e.operand))
            "isUndefined" -> Expr.IsUndef(lowerFieldForDefPred(ctx, env, e.operand))
            "isDefined"   -> Expr.IsDef(lowerFieldForDefPred(ctx, env, e.operand))
            else -> error("Unsupported unary op ${e.op}")
        }

        is Exp.BinOp -> lowerBinOp(ctx, env, e)

        is Exp.Cond -> Expr.Ite(
            lowerExp(ctx, env, e.cond).asBool(ctx),
            lowerExp(ctx, env, e.ifTrue),
            lowerExp(ctx, env, e.ifFalse)
        )

        is Exp.Call -> error("Function calls not supported in IR lowering")
        is Exp.Let -> env.shadow(e.dec.v.name, lowerExp(ctx, env, e.init)) {
            lowerExp(ctx, env, e.exp)
        }
    }

    private fun lowerBinOp(ctx: LowerCtx, env: Env, e: Exp.BinOp): Expr {
        // Pattern: (Member ==/!= UNDEFINED) → IsUndef/IsDef
        fun tryUndefinedPattern(): Expr? {
            val lMem = e.left as? Exp.Member
            val rMem = e.right as? Exp.Member
            return when {
                lMem != null && e.right is Exp.Const.UNDEFINED && e.op == "==" ->
                    Expr.IsUndef(lowerExp(ctx, Env(), lMem) as Expr.Field)
                lMem != null && e.right is Exp.Const.UNDEFINED && e.op == "!=" ->
                    Expr.IsDef(lowerExp(ctx, Env(), lMem) as Expr.Field)
                rMem != null && e.left is Exp.Const.UNDEFINED && e.op == "==" ->
                    Expr.IsUndef(lowerExp(ctx, Env(), rMem) as Expr.Field)
                rMem != null && e.left is Exp.Const.UNDEFINED && e.op == "!=" ->
                    Expr.IsDef(lowerExp(ctx, Env(), rMem) as Expr.Field)
                else -> null
            }
        }
        tryUndefinedPattern()?.let { return it }

        val l = lowerExp(ctx, env, e.left)
        val r = lowerExp(ctx, env, e.right)

        return when (e.op) {
            // arithmetic …
            "+" -> Expr.Add(l, r)
            "-" -> Expr.Sub(l, r)
            "*" -> Expr.Mul(l, r)
            "/" -> Expr.Div(l, r)

            // comparisons …
            "==" -> Expr.Eq(l, r)
            "!=" -> Expr.Ne(l, r)
            "<"  -> Expr.Lt(l, r)
            "<=" -> Expr.Le(l, r)
            ">"  -> Expr.Gt(l, r)
            ">=" -> Expr.Ge(l, r)

            // boolean connectives …
            "&&" -> Expr.And(l.asBool(ctx), r.asBool(ctx))
            "||" -> Expr.Or(l.asBool(ctx), r.asBool(ctx))

            // NEW: biconditional (boolean equivalence)
            "<->" -> Expr.Eq(l.asBool(ctx), r.asBool(ctx))

            // (Optional) implication
            "->"  -> Expr.Or(Expr.Not(l.asBool(ctx)), r.asBool(ctx))

            else -> error("Unsupported binary op ${e.op}")
        }

    }

    private class LowerCtx(
        prog: ProgramAst,
        val roles: Set<Role>
    ) {
        val typeDefs: Map<String, TypeExp> = prog.types.mapKeys { it.key.name }

        // last producer for Exp.Member(role, field) resolution
        val lastProducer: MutableMap<Pair<Role, String>, MoveId> = linkedMapOf()

        // NEW: the IR type of each concrete field produced by a move
        val fieldTypeByProducer: MutableMap<Pair<MoveId, String>, Type> = linkedMapOf()

        fun freshMoveId(blockIndex: Int, idxInBlock: Int, k: Kind, r: Role): MoveId =
            MoveId("${blockIndex}_${idxInBlock}_${k.name.lowercase()}_${sanitize(r.name)}")
    }

    private fun Expr.asBool(ctx: LowerCtx): Expr = when (this) {
        is Expr.Bool,
        is Expr.And, is Expr.Or, is Expr.Not,
        is Expr.Eq,  is Expr.Ne, is Expr.Lt, is Expr.Le, is Expr.Gt, is Expr.Ge,
        is Expr.IsDef, is Expr.IsUndef,
        is Expr.Ite -> this

        is Expr.Field -> {
            val t = ctx.fieldTypeByProducer[this.move to this.param]
                ?: error("Unknown field type for $this (producer not registered?)")
            require(t == Type.BoolType) {
                "Expected boolean expression, got non-boolean field $this"
            }
            this
        }

        else -> error("Expected boolean expression, got $this")
    }

    // ---------- Utils ----------

    private fun sanitize(s: String): String = s.replace(Regex("[^A-Za-z0-9_]"), "_")
}

fun compileToIR(ast: ProgramAst) : ProgramIR = AstToIr.lower(ast)
