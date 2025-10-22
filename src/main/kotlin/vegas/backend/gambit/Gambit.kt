package vegas.backend.gambit

import vegas.FieldRef
import vegas.Rational
import vegas.RoleId
import vegas.VarId
import vegas.frontend.Exp.Const
import vegas.frontend.Exp.Const.Num


typealias OutcomeType = Num

/**
 * Represents an extensive form game tree with better type safety and clearer semantics.
 */
sealed class GameTree {
    /**
     * A decision/chance node in the game tree.
     * @property owner The role making the decision
     * @property infosetId Unique identifier for the information set
     * @property choices Available actions and their successor nodes
     * @property isChance Whether this is a chance node
     */
    data class Decision(
        val owner: RoleId,
        val infosetId: InfosetId,
        val choices: List<Choice>,
        val isChance: Boolean = false
    ) : GameTree() {
        init {
            require(choices.isNotEmpty()) { "Decision node must have at least one choice" }
            if (isChance) {
                require(choices.all { it.probability != null }) {
                    "Chance nodes must have probabilities"
                }
                // Validate probabilities sum to 1
                val sum = choices.mapNotNull { it.probability }.fold(Rational(0, 1)) { acc, r -> acc + r }
                require(sum == Rational(1, 1)) {
                    "Chance node probabilities must sum to 1, got $sum"
                }
            }
        }
    }

    /**
     * A terminal node with payoffs.
     */
    data class Terminal(
        val payoffs: Map<RoleId, OutcomeType>
    ) : GameTree()

    /**
     * A single choice/action with its outcome.
     */
    data class Choice(
        val action: Map<VarId, Const>,
        val subtree: GameTree,
        val probability: Rational? = null  // Only for chance nodes
    )
}

/**
 * Unique identifier for an information set, based on the role and
 * the visible information available to that role.
 */
data class InfosetId(
    val role: RoleId,
    val visibleState: Map<FieldRef, Const>
) {
    // Sequential numbering within each role
    var number: Int = 0
}

// ============================================================================
// Information Set Management
// ============================================================================

/**
 * Manages information set identification and numbering.
 */
class InfosetManager {
    private val infosetMap = mutableMapOf<InfosetId, Int>()
    private val counters = mutableMapOf<RoleId, Int>()

    /**
     * Get or create an information set ID for the given role and visible state.
     */
    fun getInfosetNumber(role: RoleId, visibleState: Map<FieldRef, Const>): Int {
        val key = InfosetId(role, visibleState)
        return infosetMap.getOrPut(key) {
            val count = counters.getOrDefault(role, 0) + 1
            counters[role] = count
            count
        }
    }

    fun reset() {
        infosetMap.clear()
        counters.clear()
    }
}
