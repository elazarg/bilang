package vegas

import vegas.Exp.*
import vegas.Exp.Const.*

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
        val owner: Role,
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
            }
        }
    }

    /**
     * A terminal node with payoffs.
     */
    data class Terminal(
        val payoffs: Map<Role, OutcomeType>
    ) : GameTree()

    /**
     * A single choice/action with its outcome.
     */
    data class Choice(
        val action: Map<Var, Const>,
        val subtree: GameTree,
        val probability: Rational? = null  // Only for chance nodes
    )
}

/**
 * Unique identifier for an information set, based on the role and
 * the visible information available to that role.
 */
data class InfosetId(
    val role: Role,
    val visibleState: Map<Pair<Role, Var>, Const>
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
    private val counters = mutableMapOf<Role, Int>()

    /**
     * Get or create an information set ID for the given role and visible state.
     */
    fun getInfosetNumber(role: Role, visibleState: Map<Pair<Role, Var>, Const>): Int {
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

// ============================================================================
// Game Tree Builder
// ============================================================================

/**
 * Builds a game tree from Vegas AST with improved clarity and correctness.
 */
class GameTreeBuilder(
    private val types: Map<TypeExp.TypeId, TypeExp>
) {
    private val infosetManager = InfosetManager()

    /**
     * Build a game tree from the Vegas game specification.
     */
    fun build(game: Ext): GameTree {
        infosetManager.reset()
        return buildTree(game, GameState.empty())
    }

    private fun buildTree(ext: Ext, state: GameState): GameTree {
        return when (ext) {
            is Ext.BindSingle -> buildFromSingleBind(ext, state)
            is Ext.Bind -> buildFromMultiBind(ext, state)
            is Ext.Value -> buildTerminal(ext.outcome, state)
        }
    }

    private fun buildFromSingleBind(ext: Ext.BindSingle, state: GameState): GameTree {
        val query = ext.q
        val role = query.role

        return when (ext.kind) {
            Kind.JOIN -> {
                val newState = state.addRole(role)
                if (query.params.isEmpty()) {
                    buildTree(ext.ext, newState)
                } else {
                    buildDecision(query, ext.ext, newState)
                }
            }

            Kind.JOIN_CHANCE -> {
                val newState = state.addRole(role, isChance = true)
                if (query.params.isEmpty()) {
                    buildTree(ext.ext, newState)
                } else {
                    buildChanceNode(query, ext.ext, newState)
                }
            }

            Kind.YIELD -> buildDecision(query, ext.ext, state)

            Kind.REVEAL -> buildRevealNode(query, ext.ext, state)
        }
    }

    private fun buildFromMultiBind(ext: Ext.Bind, state: GameState): GameTree {
        return when (ext.kind) {
            Kind.JOIN -> {
                val newState = ext.qs.fold(state) { acc, q -> acc.addRole(q.role) }
                buildIndependentDecisions(ext.qs.filter { it.params.isNotEmpty() }, ext.ext, newState)
            }
            Kind.YIELD -> buildIndependentDecisions(ext.qs, ext.ext, state)
            else -> throw NotImplementedError("Multi-bind not implemented for ${ext.kind}")
        }
    }

    /**
     * Build a decision node where the role chooses from available actions.
     */
    private fun buildDecision(query: Query, continuation: Ext, state: GameState): GameTree {
        val role = query.role
        val packets = enumerateValidPackets(query, state)
        val infosetId = infosetManager.getInfosetNumber(role, state.visibleTo(role))

        val choices = packets.map { packet ->
            val newState = state.withChoices(query, packet)
            GameTree.Choice(
                action = packet,
                subtree = buildTree(continuation, newState)
            )
        }

        return GameTree.Decision(
            owner = role,
            infosetId = InfosetId(role, state.visibleTo(role)).apply { number = infosetId },
            choices = choices,
            isChance = false
        )
    }

    /**
     * Build a chance node with probabilities.
     */
    private fun buildChanceNode(query: Query, continuation: Ext, state: GameState): GameTree {
        val role = query.role
        val packets = enumerateValidPackets(query, state, includeQuit = false)
        val infosetId = infosetManager.getInfosetNumber(role, state.visibleTo(role))

        // Uniform distribution for chance nodes
        val prob = Rational(1, packets.size)

        val choices = packets.map { packet ->
            val newState = state.withChoices(query, packet)
            GameTree.Choice(
                action = packet,
                subtree = buildTree(continuation, newState),
                probability = prob
            )
        }

        return GameTree.Decision(
            owner = role,
            infosetId = InfosetId(role, state.visibleTo(role)).apply { number = infosetId },
            choices = choices,
            isChance = true
        )
    }

    /**
     * Build a reveal node where hidden information is disclosed.
     */
    private fun buildRevealNode(query: Query, continuation: Ext, state: GameState): GameTree {
        val role = query.role
        val infosetId = infosetManager.getInfosetNumber(role, state.visibleTo(role))

        // Reveal branch: reveal the hidden values
        val revealedState = state.revealHidden(query)
        val revealPacket = query.params.associate { (v, _) ->
            v to revealedState.getValue(role, v)
        }
        val revealChoice = GameTree.Choice(
            action = revealPacket,
            subtree = buildTree(continuation, revealedState)
        )

        // For non-chance nodes, also include quit option
        val choices = if (state.isChance(role)) {
            listOf(revealChoice)
        } else {
            val quitState = state.withQuit(query)
            val quitPacket = query.params.associate { (v, _) -> v to UNDEFINED }
            val quitChoice = GameTree.Choice(
                action = quitPacket,
                subtree = buildTree(continuation, quitState)
            )
            listOf(revealChoice, quitChoice)
        }

        return GameTree.Decision(
            owner = role,
            infosetId = InfosetId(role, state.visibleTo(role)).apply { number = infosetId },
            choices = choices,
            isChance = state.isChance(role)
        )
    }

    // Build independent simultaneous decisions for multiple roles.
    // Infosets are computed once from the *same* pre-move state.
    // Action enumeration (where-clauses) is also evaluated on that same pre-move state.
    // Subtrees are built after accumulating choices, but infoset IDs never depend on later players' choices.
    private fun buildIndependentDecisions(
        queries: List<Query>,
        continuation: Ext,
        state: GameState
    ): GameTree {
        if (queries.isEmpty()) return buildTree(continuation, state)

        // All roles moving now (simultaneously)
        val simRoles: Set<Role> = queries.map { it.role }.toSet()

        // 1) Precompute infosets for all roles from the SAME pre-move snapshot.
        //    No choice is yet written to the heap, and we exclude simultaneous roles from visibility.
        val preInfosets: Map<Query, InfosetId> =
            queries.associateWith { q ->
                val view = state.visibleTo(q.role, excludeRoles = simRoles)
                val number = infosetManager.getInfosetNumber(q.role, view)
                InfosetId(q.role, view).apply { this.number = number }
            }

        // 2) Pre-enumerate legal action packets for each role from the SAME pre-move snapshot.
        //    This guarantees that where-clauses cannot depend on other simultaneous choices.
        val preEdges: Map<Query, List<Map<Var, Const>>> =
            queries.associateWith { q -> enumerateValidPackets(q, state) }

        // 3) Build the cross-product of choices. We accumulate choices into the state,
        //    but never recompute infosets (they remain the ones in `preInfosets`).
        fun recurse(i: Int, accState: GameState): GameTree {
            if (i == queries.size) {
                // After all have moved, continue the game.
                return buildTree(continuation, accState)
            }

            val q = queries[i]
            val edges = preEdges.getValue(q)
            val infosetId = preInfosets.getValue(q)

            val choices = edges.map { packet ->
                val nextState = accState.withChoices(q, packet)
                GameTree.Choice(
                    action = packet,
                    subtree = recurse(i + 1, nextState)
                )
            }

            return GameTree.Decision(
                owner = q.role,
                infosetId = infosetId,
                choices = choices,
                isChance = false
            )
        }

        return recurse(0, state)
    }


    /**
     * Build a terminal node with payoffs.
     */
    private fun buildTerminal(outcome: Outcome, state: GameState): GameTree.Terminal {
        val desugared = desugar(outcome)
        val payoffs = desugared.ts.mapValues { (_, exp) ->
            state.eval(exp) as OutcomeType
        }
        return GameTree.Terminal(payoffs)
    }

    /**
     * Enumerate all valid action packets satisfying the where clause.
     */
    private fun enumerateValidPackets(
        query: Query,
        state: GameState,
        includeQuit: Boolean = true
    ): List<Map<Var, Const>> {
        val validPackets = query.params
            .associate { (v, type) -> v to enumerateValues(type) }
            .cartesianProduct()
            .filter { packet -> state.eval(query.where, query, packet) == Bool(true) }

        return if (includeQuit && !state.isChance(query.role) && !state.hasQuit(query.role)) {
            val quitPacket = query.params.associate { (v, _) -> v to UNDEFINED }
            validPackets + quitPacket
        } else {
            validPackets
        }
    }

    /**
     * Enumerate all possible values for a type.
     */
    private fun enumerateValues(type: TypeExp): List<Const> = when (type) {
        is TypeExp.Subset -> type.values.toList()
        TypeExp.BOOL -> listOf(Bool(true), Bool(false))
        is TypeExp.Hidden -> enumerateValues(type.type).map { Hidden(it) }
        is TypeExp.TypeId -> enumerateValues(types.getValue(type))
        else -> throw NotImplementedError("Cannot enumerate $type")
    }
}

// ============================================================================
// Game State Management
// ============================================================================

/**
 * Represents the state of the game during tree construction.
 * Tracks role participation, variable bindings, and hidden information.
 */
data class GameState(
    private val globals: Map<Var, Const> = emptyMap(),
    private val roles: Map<Role, RoleState> = emptyMap(),
    private val heap: Map<Pair<Role, Var>, Const> = emptyMap()
) {
    data class RoleState(
        val address: Int,  // 0 for chance
        val hasQuit: Boolean = false
    )

    companion object {
        fun empty() = GameState()
    }

    fun addRole(role: Role, isChance: Boolean = false): GameState {
        val address = if (isChance) 0 else {
            1 + (roles.values.maxOfOrNull { it.address } ?: 0)
        }
        return copy(roles = roles + (role to RoleState(address)))
    }

    fun isChance(role: Role): Boolean =
        roles[role]?.address == 0

    fun hasQuit(role: Role): Boolean =
        roles[role]?.hasQuit == true

    fun withChoices(query: Query, packet: Map<Var, Const>): GameState {
        val newHeap = heap + packet.map { (v, const) -> (query.role to v) to const }
        return copy(heap = newHeap)
    }

    fun withQuit(query: Query): GameState {
        val quitHeap = query.params.associate { (v, _) ->
            (query.role to v) to UNDEFINED
        }
        val newRoles = roles + (query.role to roles.getValue(query.role).copy(hasQuit = true))
        return copy(heap = heap + quitHeap, roles = newRoles)
    }

    fun revealHidden(query: Query): GameState {
        val revealed = heap.mapValues { (key, value) ->
            if (key.first == query.role && value is Hidden) {
                value.value
            } else {
                value
            }
        }
        return copy(heap = revealed)
    }

    /**
     * Get the visible state for a specific role (excluding hidden info from others).
     */
    fun visibleTo(role: Role, excludeRoles: Set<Role> = emptySet()): Map<Pair<Role, Var>, Const> {
        return heap.mapValues { (key, value) ->
            val (r, _) = key
            when {
                r in excludeRoles -> Hidden(UNDEFINED)
                r != role && value is Hidden -> Hidden(UNDEFINED)
                else -> value
            }
        }
    }

    fun getValue(role: Role, field: Var): Const =
        heap.getValue(role to field)

    /**
     * Evaluate an expression in the current state.
     */
    fun eval(exp: Exp, query: Query? = null, packet: Map<Var, Const> = emptyMap()): Const {
        val env = Env(globals, roles.keys.associateWith { Address(roles.getValue(it).address) }, heap)
        val extendedEnv = if (query != null) {
            env.copy(h = env.h + packet.map { (v, c) -> (query.role to v) to c })
        } else {
            env
        }
        return eval(exp, extendedEnv)
    }
}

// ============================================================================
// EFG Format Writer
// ============================================================================

/**
 * Writes game trees in Gambit's EFG format with proper formatting.
 */
class EfgWriter(
    private val gameName: String,
    private val gameDescription: String,
    private val players: List<Role>
) {
    private var outcomeCounter = 1

    fun write(tree: GameTree): String {
        outcomeCounter = 1
        val header = buildHeader()
        val nodes = writeTree(tree)
        return "$header\n\n${nodes.joinToString("\n")}"
    }

    private fun buildHeader(): String {
        val playerList = players.joinToString(" ") { "\"${it.name}\"" }
        return """EFG 2 R "$gameName" { $playerList }
"$gameDescription""""
    }

    private fun writeTree(tree: GameTree): List<String> {
        return when (tree) {
            is GameTree.Decision -> writeDecision(tree)
            is GameTree.Terminal -> listOf(writeTerminal(tree))
        }
    }

    private fun writeDecision(node: GameTree.Decision): List<String> {
        val nodeType = if (node.isChance) "c" else "p"
        val nodeName = "\"\""

        val line = if (node.isChance) {
            val owner = ""
            val infosetNum = node.infosetId.number
            val infosetName = "\"\""
            val actions = node.choices.joinToString(" ") { choice ->
                val actionName = formatActionName(choice.action)
                val prob = choice.probability ?: Rational(1)
                "\"$actionName\" ${formatRational(prob)}"
            }
            "$nodeType $nodeName $infosetNum $infosetName { $actions } 0"
        } else {
            val owner = players.indexOf(node.owner) + 1
            val infosetNum = node.infosetId.number
            val infosetName = "\"\""
            val actions = node.choices.joinToString(" ") { choice ->
                val actionName = formatActionName(choice.action)
                "\"$actionName\""
            }
            "$nodeType $nodeName $owner $infosetNum $infosetName { $actions } 0"
        }

        val subtrees = node.choices.flatMap { writeTree(it.subtree) }
        return listOf(line) + subtrees
    }

    private fun writeTerminal(node: GameTree.Terminal): String {
        val nodeName = "\"\""
        val outcomeNum = outcomeCounter++
        val outcomeName = "\"\""
        val payoffs = players.joinToString(" ") { role ->
            node.payoffs[role]?.n?.toString() ?: "0"
        }
        return "t $nodeName $outcomeNum $outcomeName { $payoffs }"
    }

    private fun formatActionName(action: Map<Var, Const>): String {
        return action.values.joinToString("&") { formatValue(it) }
    }

    private fun formatValue(const: Const): String = when (const) {
        is Bool -> const.truth.toString()
        is Num -> const.n.toString()
        is Hidden -> "Hidden(${formatValue(const.value)})"
        UNDEFINED -> "None"
        else -> const.toString()
    }

    private fun formatRational(r: Rational): String {
        return if (r.denominator == 1) {
            r.numerator.toString()
        } else {
            "${r.numerator}/${r.denominator}"
        }
    }
}

// ============================================================================
// Utility Extensions
// ============================================================================

/**
 * Compute Cartesian product of variable assignments.
 */
private fun Map<Var, List<Const>>.cartesianProduct(): List<Map<Var, Const>> {
    return entries
        .map { (key, values) -> values.map { key to it } }
        .fold(listOf(emptyList<Pair<Var, Const>>())) { acc, pairs ->
            pairs.flatMap { pair -> acc.map { list -> list + pair } }
        }
        .map { it.toMap() }
}

// ============================================================================
// Main API
// ============================================================================

/**
 * Main class for extensive form game generation.
 */
class ExtensiveFormGame(
    private val name: String,
    private val description: String,
    private val players: List<Role>,
    private val tree: GameTree
) {
    fun toEfg(): String {
        val writer = EfgWriter(name, description, players)
        return writer.write(tree)
    }

    override fun toString(): String = toEfg()
}

/**
 * Build an extensive form game from a Vegas program.
 */
fun buildExtensiveFormGame(program: ExpProgram): ExtensiveFormGame {
    val players = findRoles(program.game)
    val builder = GameTreeBuilder(program.types)
    val tree = builder.build(program.game)

    return ExtensiveFormGame(
        name = program.name.ifEmpty { "Game" },
        description = program.desc.ifEmpty { "Generated by Vegas" },
        players = players,
        tree = tree
    )
}
