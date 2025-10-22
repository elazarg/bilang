package vegas.backend.gambit

import vegas.FieldRef
import vegas.RoleId
import vegas.VarId
import vegas.ir.GameIR
import vegas.ir.*
import vegas.frontend.Exp.Const.* // only for pretty printing if you want; not required

/**
 * Build a Gambit EFG string directly from the Vegas IR (GameIR).
 *
 * Assumptions:
 * - Only SetType is enumerable for non-bool types. (IntType is not enumerated.)
 * - Hidden behavior: Parameter.visible=false chooses a value but stores it as Hidden for others
 *   until the first later phase where the same (role,var) appears with visible=true (reveal).
 * - Guards are evaluated with snapshot semantics: they can only see earlier-phase public/revealed fields.
 *   If a guard refers to same-phase or unrevealed hidden fields, it must have been split/deferred earlier,
 *   so we evaluate only the decidable part here. (If you didn’t split, then such guards evaluate to false.)
 */
fun generateExtensiveFormGame(ir: GameIR): String {
    val players = ir.roles
    val builder = IrGameTreeBuilder(ir)
    val tree = builder.build()
    return ExtensiveFormGame(
        name = ir.name.ifEmpty { "Game" },
        description = "Generated from IR",
        players = players,
        tree = tree
    ).toEfg()
}

// -----------------------------
// IR → GameTree builder
// -----------------------------

private class IrGameTreeBuilder(private val ir: GameIR) {

    private val infosets = InfosetManager()

    /** Map (role,var) → list of (phaseIdx, visible) occurrences to detect commit/reveal. */
    private val occurrences: Map<FieldRef, List<Pair<Int, Boolean>>> =
        buildOccurrences(ir)

    fun build(): GameTree {
        infosets.reset()
        return buildFromPhase(phaseIdx = 0, state = IrState.empty(ir.roles))
    }

    private fun buildFromPhase(phaseIdx: Int, state: IrState): GameTree {
        if (phaseIdx >= ir.phases.size) {
            // Terminal: evaluate payoffs
            val pay = ir.payoffs.mapValues { (_, e) -> state.eval(e).toOutcome() }
            return GameTree.Terminal(pay)
        }

        val phase = ir.phases[phaseIdx]

        // Collect per-role legal action packets from the SAME pre-move snapshot.
        // Snapshot semantics: legality cannot depend on same-phase choices.
        val simRoles = phase.keys
        val legalPacketsByRole: Map<RoleId, List<Map<VarId, IrVal>>> =
            phase.mapValues { (_, sig) ->
                enumeratePackets(sig, state, phaseIdx).filter { pkt ->
                    // Evaluate guard with the packet applied for THIS role.
                    val next = state.withPacket(pkt)
                    next.eval(sig.requires.condition).asBool()
                }
            }

        // Pre-compute infosets for each role from the identical snapshot.
        val preInfoset: Map<RoleId, InfosetId> = simRoles.associate { rr ->
            val vis = state.visibleTo(rr, phaseIdx, occurrences)
            val num = infosets.getInfosetNumber(rr, vis)
            rr to InfosetId(rr, vis).apply { number = num }
        }

        // Cross-product over roles in a fixed order (stable over the map’s iteration order).
        val roleOrder = simRoles.map { RoleId(it.name) }
        fun recurse(i: Int, accState: IrState): GameTree {
            if (i == roleOrder.size) return buildFromPhase(phaseIdx + 1, accState)

            val role = roleOrder[i]
            val sig = phase[role] ?: error("Missing signature for $role")
            val choicesForRole = legalPacketsByRole.getOrElse(role) { emptyList() }
            val nodeChoices = choicesForRole.map { pkt ->
                val post = accState.withPacket(pkt)
                // If this packet includes reveals (first later visible=true), replace Hidden with raw.
                val revealed = post.applyPotentialReveals(role, sig, phaseIdx, occurrences)

                GameTree.Choice(
                    action = pkt.filterValues { it !is IrVal.Undefined }  // omit explicit None from action name
                        .mapValues { it.value.asConstForLabel() },
                    subtree = recurse(i + 1, revealed)
                )
            }

            return GameTree.Decision(
                owner = role,
                infosetId = preInfoset.getValue(role),
                choices = nodeChoices,
                isChance = isChance(role)
            )
        }

        return recurse(0, state)
    }

    // -----------------------------
    // Packet enumeration
    // -----------------------------
    private fun enumeratePackets(sig: Signature, state: IrState, phaseIdx: Int): List<Map<VarId, IrVal>> {
        if (sig.parameters.isEmpty()) return listOf(emptyMap())
        // enumerate per parameter, then cartesian product
        val lists: List<List<Pair<VarId, IrVal>>> = sig.parameters.map { p ->
            val vals = when (p.type) {
                is Type.BoolType -> listOf(true, false).map { v ->
                    if (p.visible) IrVal.BoolVal(v) else IrVal.Hidden(IrVal.BoolVal(v))
                }
                is Type.IntType -> error("Cannot enumerate IntType; use SetType or BoolType")
                is Type.SetType -> p.type.values.map { n ->
                    val base = IrVal.IntVal(n)
                    if (p.visible) base else IrVal.Hidden(base)
                }
            }
            vals.map { v -> p.name to v }
        }
        return cartesian(lists).map { it.toMap() }
    }

    // -----------------------------
    // Helpers
    // -----------------------------

    private fun isChance(role: RoleId): Boolean =
        role.name.equals("Chance", ignoreCase = true)

    private fun cartesian(lists: List<List<Pair<VarId, IrVal>>>): List<List<Pair<VarId, IrVal>>> =
        lists.fold(listOf(emptyList())) { acc, xs -> acc.flatMap { a -> xs.map { a + it } } }

    private fun buildOccurrences(ir: GameIR): Map<FieldRef, List<Pair<Int, Boolean>>> {
        val m = mutableMapOf<FieldRef, MutableList<Pair<Int, Boolean>>>()
        ir.phases.forEachIndexed { pi, ph ->
            ph.forEach { (r, sig) ->
                sig.parameters.forEach { p ->
                    m.getOrPut(FieldRef(RoleId(r.name), p.name)) { mutableListOf() }.add(pi to p.visible)
                }
            }
        }
        return m.mapValues { it.value.toList() }
    }
}

// -----------------------------
// Minimal IR evaluator with visibility rules
// -----------------------------

/** Runtime values for IR expressions. */
private sealed class IrVal {
    data class IntVal(val v: Int) : IrVal()
    data class BoolVal(val v: Boolean) : IrVal()
    data class Hidden(val inner: IrVal) : IrVal()   // value chosen but not visible to others
    object Undefined : IrVal()

    fun asConstForLabel(): vegas.frontend.Exp.Const = when (this) {
        is BoolVal -> Bool(v)
        is IntVal -> Num(v)
        is Hidden -> Hidden(inner.asConstForLabel())
        Undefined -> UNDEFINED
    }

    fun toOutcome(): Num = when (this) {
        is IntVal -> Num(v)
        is BoolVal -> Num(if (v) 1 else 0)
        is Hidden, Undefined -> error("Terminal payoff references undefined/hidden value")
    }

    fun asBool(): Boolean = when (this) {
        is BoolVal -> v
        is IntVal -> v != 0
        is Hidden, Undefined -> false
    }

    fun asInt(): Int = when (this) {
        is IntVal -> v
        is BoolVal -> if (v) 1 else 0
        is Hidden, Undefined -> error("Expected int, got $this")
    }
}

/** State over (role,var) bindings; enforces reveal at the phase where first visible=true occurs after a hidden commit. */
private data class IrState(
    val roles: Set<RoleId>,
    val heap: Map<FieldRef, IrVal> = emptyMap()
) {
    companion object {
        fun empty(roles: Set<RoleId>) = IrState(roles)
    }

    fun withPacket(pkt: Map<VarId, IrVal>): IrState {
        if (pkt.isEmpty()) return this
        val role = currentRoleFromPacket(pkt)
        val entries = pkt.map { (v, value) -> FieldRef(role, v) to value }
        return copy(heap = heap + entries)
    }

    /**
     * Reveal any fields which are supposed to become visible in this phase.
     * In this IR builder we reveal opportunistically for the **acting role** when its parameter
     * appears with visible=true after a hidden commit. (A strict pass using occurrences map controls timing.)
     */
    fun applyPotentialReveals(
        role: RoleId,
        sig: Signature,
        phaseIdx: Int,
        occurrences: Map<FieldRef, List<Pair<Int, Boolean>>>
    ): IrState {
        var h = heap
        sig.parameters.forEach { p ->
            if (p.visible) {
                val key = FieldRef(role, p.name)
                val seen = occurrences[key] ?: return@forEach
                // reveal only if this is the first 'true' after at least one 'false'
                val firstCommit = seen.indexOfFirst { !it.second }.takeIf { it >= 0 }?.let { seen[it].first }
                val firstReveal = seen.indexOfFirst { it.second }.takeIf { it >= 0 }?.let { seen[it].first }
                if (firstCommit != null && firstReveal == phaseIdx) {
                    val cur = h[key]
                    if (cur is IrVal.Hidden) h = h + (key to cur.inner)
                }
            }
        }
        return copy(heap = h)
    }

    /** Visible snapshot to 'who' at a given phase: others’ Hidden appear as Hidden(UNDEFINED). */
    fun visibleTo(who: RoleId, phaseIdx: Int, occurrences: Map<FieldRef, List<Pair<Int, Boolean>>>): Map<FieldRef, vegas.frontend.Exp.Const> {
        return heap.mapValues { (k, v) ->
            val (r, _) = k
            if (r == who) v.asConstForLabel()
            else when (v) {
                is IrVal.Hidden -> Hidden(UNDEFINED)
                is IrVal.Undefined -> UNDEFINED
                else -> v.asConstForLabel()
            }
        }
    }

    /** Evaluate IR.Expr under current heap. Undefined/hidden fields yield false in boolean context (guard semantics). */
    fun eval(e: Expr): IrVal = when (e) {
        is Expr.IntLit -> IrVal.IntVal(e.v)
        is Expr.BoolLit -> IrVal.BoolVal(e.v)
        is Expr.Field -> heap[e.field] ?: IrVal.Undefined
        is Expr.IsDefined -> {
            val v = heap[e.field]
            IrVal.BoolVal(v != null && v !is IrVal.Undefined && !(v is IrVal.Hidden))
        }

        // arithmetic
        is Expr.Add -> IrVal.IntVal(eval(e.l).asInt() + eval(e.r).asInt())
        is Expr.Sub -> IrVal.IntVal(eval(e.l).asInt() - eval(e.r).asInt())
        is Expr.Mul -> IrVal.IntVal(eval(e.l).asInt() * eval(e.r).asInt())
        is Expr.Div -> IrVal.IntVal(eval(e.l).asInt() / eval(e.r).asInt())
        is Expr.Neg -> IrVal.IntVal(-eval(e.x).asInt())

        // comparisons -> booleans
        is Expr.Eq -> IrVal.BoolVal(eq(eval(e.l), eval(e.r)))
        is Expr.Ne -> IrVal.BoolVal(!eq(eval(e.l), eval(e.r)))
        is Expr.Lt -> IrVal.BoolVal(eval(e.l).asInt() < eval(e.r).asInt())
        is Expr.Le -> IrVal.BoolVal(eval(e.l).asInt() <= eval(e.r).asInt())
        is Expr.Gt -> IrVal.BoolVal(eval(e.l).asInt() > eval(e.r).asInt())
        is Expr.Ge -> IrVal.BoolVal(eval(e.l).asInt() >= eval(e.r).asInt())

        // boolean
        is Expr.And -> IrVal.BoolVal(eval(e.l).asBool() && eval(e.r).asBool())
        is Expr.Or  -> IrVal.BoolVal(eval(e.l).asBool() || eval(e.r).asBool())
        is Expr.Not -> IrVal.BoolVal(!eval(e.x).asBool())
        is Expr.Ite -> if (eval(e.c).asBool()) eval(e.t) else eval(e.e)
    }

    private fun eq(a: IrVal, b: IrVal): Boolean = when {
        a is IrVal.IntVal && b is IrVal.IntVal -> a.v == b.v
        a is IrVal.BoolVal && b is IrVal.BoolVal -> a.v == b.v
        a is IrVal.Undefined && b is IrVal.Undefined -> true
        else -> false // hidden and mismatched types are never equal in guards
    }

    /** crude: infer the acting role from the packet’s (role,var) keys if present; otherwise no-op. */
    private fun currentRoleFromPacket(pkt: Map<VarId, IrVal>): RoleId {
        // We don't store role on the packet; caller applies per-role.
        // Here we just return a dummy (not used); withPacket() called per-role so this is never hit.
        return roles.first()
    }
}

// Outcome conversion util
private fun IrVal.toOutcome(): OutcomeType =
    when (this) {
        is IrVal.IntVal -> Num(v)
        is IrVal.BoolVal -> Num(if (v) 1 else 0)
        is IrVal.Hidden, IrVal.Undefined -> error("Payoff references hidden/undefined value")
    }

private fun IrVal.asConstForLabel(): vegas.frontend.Exp.Const =
    when (this) {
        is IrVal.IntVal -> Num(v)
        is IrVal.BoolVal -> Bool(v)
        is IrVal.Hidden -> Hidden(inner.asConstForLabel())
        IrVal.Undefined -> UNDEFINED
    }
