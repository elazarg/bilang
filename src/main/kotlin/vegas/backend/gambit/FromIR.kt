package vegas.backend.gambit

import vegas.FieldRef
import vegas.Rational
import vegas.RoleId
import vegas.StaticError
import vegas.VarId
import vegas.ir.GameIR
import vegas.ir.*

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
    val builder = IrGameTreeBuilder(ir)
    val tree = builder.build()
    return ExtensiveFormGame(
        name = ir.name.ifEmpty { "Game" },
        description = "Generated from IR",
        strategicPlayers = ir.roles,
        tree = tree
    ).toEfg()
}

private typealias PhaseMap = Map<FieldRef, IrVal>

/** Visible snapshot to 'who' at a given phase: others’ Hidden appear as Hidden(UNDEFINED). */
private fun redacted(messages: PhaseMap, who: RoleId): PhaseMap {
    return messages.mapValues { (fieldRef, v) ->
        val (r, _) = fieldRef
        if (r == who) v
        else when (v) {
            is IrVal.Hidden -> IrVal.Undefined
            else -> v
        }
    }
}

/**
 * Unique identifier for an information set, based on the role and
 * the visible information available to that role.
 * Each role knows exactly the set of messages sent before the current choice node,
 * after erasing the content of messages that are hidden (commitments).
 * It is designed as an explicit stack (functional list) instead of List, to make recursion trivial
 */
private data class Infoset(val lastPhase: PhaseMap = mapOf(), val past: Infoset? = null) {
    fun get(f: FieldRef): IrVal = lastPhase[f] ?: (past?.get(f) ?: IrVal.Undefined)
    infix fun with(newPhase: PhaseMap): Infoset = Infoset(newPhase, this)
}

private typealias KnowledgeMap = Map<RoleId, Infoset>


/** Evaluate IR.Expr under current heap. Undefined/hidden fields yield false in boolean context (guard semantics). */
private fun eval(heap: Infoset, e: Expr): IrVal {
    fun eval(e: Expr): IrVal = when (e) {
        is Expr.IntVal -> IrVal.IntVal(e.v)
        is Expr.BoolVal -> IrVal.BoolVal(e.v)
        is Expr.Field -> heap.get(e.field)
        is Expr.IsDefined -> {
            val v = heap.get(e.field)
            IrVal.BoolVal(v !is IrVal.Undefined && v !is IrVal.Hidden)
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
        is Expr.Or -> IrVal.BoolVal(eval(e.l).asBool() || eval(e.r).asBool())
        is Expr.Not -> IrVal.BoolVal(!eval(e.x).asBool())
        is Expr.Ite -> if (eval(e.c).asBool()) eval(e.t) else eval(e.e)
    }
    return eval(e)
}

private fun eq(a: IrVal, b: IrVal): Boolean = when {
    a is IrVal.IntVal && b is IrVal.IntVal -> a.v == b.v
    a is IrVal.BoolVal && b is IrVal.BoolVal -> a.v == b.v
    a is IrVal.Undefined && b is IrVal.Undefined -> true
    else -> false // hidden and mismatched types are never equal in guards
}

/** State over (role,var) bindings; enforces reveal at the phase where first visible=true occurs after a hidden commit. */
private typealias State = Infoset

private fun toPhaseMap(role: RoleId, pkt: Map<VarId, IrVal>): PhaseMap {
    return pkt.mapKeys { (v, _) -> FieldRef(role, v) }
}

private fun State.hasUndefined(role: RoleId): Boolean {
    return lastPhase.any {p->p.key.role == role && p.value == IrVal.Undefined } || past?.hasUndefined(role) ?: false
}

/**
 * Manages information set identification and numbering.
 */
private class InfosetManager(val roles: Set<RoleId>) {
    private val counters = roles.associateWith<RoleId, MutableMap<Infoset, Int>> { mutableMapOf() }
    private var chanceCounter: Int = 0

    /**
     * Get or create an information set ID for the given role and visible state.
     */
    fun getInfosetNumber(role: RoleId, key: Infoset): Int {
        if (role !in roles) {
            chanceCounter += 1
            return chanceCounter
        }
        return counters.getValue(role).getOrPut(key) { counters.getValue(role).size }
    }
}

private class IrGameTreeBuilder(private val ir: GameIR) {

    private val infosets = InfosetManager(ir.roles)

    // This is the set of "real" players
    private val strategicPlayers: Set<RoleId> = ir.roles

    fun build(): GameTree {
        return buildFromPhase(phaseIdx = 0, state = State(), (ir.roles + ir.chanceRoles).associateWith { Infoset() })
    }

    private fun buildFromPhase(phaseIdx: Int, state: State, knowledgeMap: KnowledgeMap): GameTree {
        if (phaseIdx >= ir.phases.size) {
            // Terminal: evaluate payoffs
            val pay = ir.payoffs.mapValues { (_, e) -> eval(state, e).toOutcome() }
            return GameTree.Terminal(pay)
        }

        val phase = ir.phases[phaseIdx]

        // Collect per-role legal action packets from the SAME pre-move snapshot.
        // Snapshot semantics: legality cannot depend on same-phase choices.
        val legalPacketsByRole: Map<RoleId, List<Map<VarId, IrVal>>> =
            phase.actions.mapValues { (role, sig) ->
                enumeratePackets(sig, state, role).filter { pkt ->
                    // Evaluate guard with the packet applied for THIS role.
                    eval(Infoset(toPhaseMap(role, pkt), state), sig.requires.condition).asBool()
                }
            }

        val simRoles = phase.roles()
        // Cross-product over roles in a fixed order (stable over the map’s iteration order).
        val roleOrder = simRoles.toList()
        fun recurse(i: Int, accState: PhaseMap = mapOf()): GameTree {
            if (i == roleOrder.size) {
                // reveal the non-hidden messages from the current phase:
                val newKnowledgeMap: KnowledgeMap =
                    knowledgeMap.mapValues { (role, knowledge) -> knowledge with redacted(accState, role) }
                val newState = Infoset(accState, state)
                return buildFromPhase(phaseIdx + 1, newState, newKnowledgeMap)
            }
            val role = roleOrder[i]

            // side effect - get a lower number
            val infosetId = infosets.getInfosetNumber(role, knowledgeMap.getValue(role))

            val sig = phase.signature(role) ?: error("Missing signature for $role")
            val choicesForCurrentRole = legalPacketsByRole.getOrElse(role) { emptyList() }
            val isChanceNode = isChance(role)
            val uniformProb = if (isChanceNode) Rational(1, choicesForCurrentRole.size.coerceAtLeast(1)) else null

            // 1. Build list of all legal choices
            val explicitChoices = choicesForCurrentRole.map { pkt ->
                GameTree.Choice(
                    action = pkt.filterValues { it !is IrVal.Undefined },  // omit explicit None from action name
                    subtree = recurse(i + 1, accState + toPhaseMap(role, pkt)),
                    probability = uniformProb
                )
            }

            // 2. *** Add the "Bail" / "None" choice for strategic players ***
            val allChoices = if (isChanceNode) {
                // Chance nodes cannot "bail"
                explicitChoices
            } else {
                val defaultChoices = phase.actions.getValue(role).parameters.associate { FieldRef(role, it.name) to IrVal.Undefined }
                // Strategic players can "bail" (fail to act)
                val bailChoice = GameTree.Choice(
                    action = emptyMap(), // Renders as "None" or ""
                    subtree = recurse(i + 1, accState + defaultChoices),
                    probability = null
                )
                // Add the bail choice to the list of explicit choices
                explicitChoices + bailChoice
            }
            if (allChoices.isEmpty()) {
                throw StaticError("No choices for $role")
            }
            // 3. Handle a "no-op" phase (e.g., Race_join)
            if (sig.parameters.isEmpty()) {
                // All choices are equivalent (no parameters to choose), so just take the first
                return allChoices.first().subtree
            }

            return GameTree.Decision(
                owner = role,
                infosetId = infosetId,
                choices = allChoices,
                isChance = isChanceNode
            )
        }

        return recurse(0)
    }

    // -----------------------------
    // Packet enumeration
    // -----------------------------
    private fun enumeratePackets(sig: Signature, state: State, role: RoleId): List<Map<VarId, IrVal>> {
        if (sig.parameters.isEmpty()) return listOf(emptyMap())
        if (state.hasUndefined(role))
            return emptyList()  // No enumerated choices
        // enumerate per parameter, then cartesian product
        val lists: List<List<Pair<VarId, IrVal>>> = sig.parameters.map { p ->
            val fieldRef = FieldRef(role, p.name)
            val priorValue = state.get(fieldRef)
            val vals = when {
                // If revealing a hidden value, only allow that specific value
                priorValue is IrVal.Hidden && p.visible -> {
                    listOf(priorValue.inner)  // <= Only one choice!
                }
                // Otherwise enumerate normally
                else -> when (p.type) {
                    is Type.BoolType -> listOf(true, false).map { v ->
                        if (p.visible) IrVal.BoolVal(v) else IrVal.Hidden(IrVal.BoolVal(v))
                    }

                    is Type.IntType -> error("Cannot enumerate IntType; use SetType or BoolType")
                    is Type.SetType -> p.type.values.map { n ->
                        val base = IrVal.IntVal(n)
                        if (p.visible) base else IrVal.Hidden(base)
                    }
                }
            }
            vals.map { v -> p.name to v }
        }
        return cartesian(lists).map { it.toMap() }.filter { pkt ->
            eval(Infoset(toPhaseMap(role, pkt), state), sig.requires.condition).asBool()
        }
    }

    // -----------------------------
    // Helpers
    // -----------------------------

    private fun isChance(role: RoleId): Boolean = role !in strategicPlayers

    private fun cartesian(lists: List<List<Pair<VarId, IrVal>>>): List<List<Pair<VarId, IrVal>>> =
        lists.fold(listOf(emptyList())) { acc, xs -> acc.flatMap { a -> xs.map { a + it } } }
}

// -----------------------------
// Minimal IR evaluator with visibility rules
// -----------------------------

/** Runtime values for IR expressions. */
internal sealed class IrVal {
    data class IntVal(val v: Int) : IrVal()
    data class BoolVal(val v: Boolean) : IrVal()
    data class Hidden(val inner: IrVal) : IrVal()   // value chosen but not visible to others
    object Undefined : IrVal()

    fun toOutcome(): IntVal = when (this) {
        is IntVal -> IntVal(v)
        is BoolVal -> IntVal(if (v) 1 else 0)
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
