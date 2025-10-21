package vegas.backend.gambit

import vegas.Rational
import vegas.frontend.Role
import vegas.ir.Expr
import vegas.ir.Move
import vegas.ir.MoveId
import vegas.ir.MoveKind
import vegas.ir.ProgramIR
import vegas.ir.Type


data class EfgConfig(
    val gameName: String? = null,
    val useUniformChanceWhenMissing: Boolean = true
)

private sealed class ConstG {
    data class IntV(val v: Int) : ConstG() {
        override fun toString() = v.toString()
    }

    data class BoolV(val v: Boolean) : ConstG() {
        override fun toString() = if (v) "true" else "false"
    }

    data class EnumV(val tag: String) : ConstG() {
        override fun toString() = tag
    }
}

private typealias ChoiceTuple = List<Pair<String, ConstG>> // (paramName -> value)

/**
 * EFG emitter for Gambit (.efg). Produces extensive–form with imperfect info that encodes
 * simultaneous blocks by using a fixed expansion order and information sets derived from
 * the *pre-block* snapshot (so co-movers cannot see each other’s choices).
 */
object GambitEfgBackend {

    fun generate(protocol: ProgramIR, cfg: EfgConfig = EfgConfig()): String {
        require(protocol.blocks.isNotEmpty()) { "Protocol must have at least one block" }
        val ctx = Ctx(protocol)
        val root = Node.Root
        expandBlocks(ctx, root, 0, State())

        // Header
        val sb = StringBuilder()
        val players = protocol.roles.filter { it != Role.Chance }
        val name = cfg.gameName ?: protocol.name
        sb.appendLine("""EFG 2 R "$name" { ${players.joinToString(" ") { "\"${it.name}\"" }} }""")

        // Print tree in Gambit order
        val out = Printer(sb, players.map { it.name })
        out.emit(root, ctx)

        // Terminal payoffs
        return sb.toString()
    }

    // ---------- Internal state & helpers ----------

    /** Public/revealed store only; owners also cache hidden choices for infoset computation. */
    private data class State(
        // Public values visible to all (after their producing block) or revealed Hidden
        val publicVals: MutableMap<Pair<MoveId, String>, ConstG> = LinkedHashMap(),
        // Commitment presence (exists) and revealed flag
        val commits: MutableSet<Pair<MoveId, String>> = LinkedHashSet(),
        val revealed: MutableSet<Pair<MoveId, String>> = LinkedHashSet(),
        // Private knowledge of owners: the committed inner values (for infosets when they move later)
        val ownerSecrets: MutableMap<Pair<MoveId, String>, ConstG> = LinkedHashMap()
    ) {
        fun clone() = copy(
            publicVals = LinkedHashMap(publicVals),
            commits = LinkedHashSet(commits),
            revealed = LinkedHashSet(revealed),
            ownerSecrets = LinkedHashMap(ownerSecrets)
        )
    }

    private class Ctx(val p: ProgramIR) {
        val moveIndex: Map<MoveId, Int> =
            p.blocks.flatMapIndexed { bi, b -> b.moves.map { it.id to bi } }.toMap()

        val chanceWeights: Map<MoveId, Map<ConstG, Rational>> = emptyMap()

        val dom = HashMap<Type, List<ConstG>>()

        val topLevel: MutableList<Node.Decision> = mutableListOf()
    }

    // ---------- Tree nodes ----------

    private sealed class Node {
        object Root : Node()
        class Decision(
            val player: Role,                      // Role or Chance
            val infoKey: InfoKey?,                 // null for Chance / terminals
            val actions: MutableList<ActionEdge> = mutableListOf()
        ) : Node()

        class Terminal(val payoffs: Array<Rational>) : Node()
    }

    private data class ActionEdge(
        val label: String,
        val prob: Rational?,         // only for chance; otherwise null
        val child: Node
    )

    /** Knowledge key defining an infoset for a given role at a given decision. */
    private data class InfoKey(val role: Role, val signature: String)

    // ---------- Expansion ----------

    private fun expandBlocks(ctx: Ctx, parent: Node, blockIdx: Int, state: State) {
        if (blockIdx >= ctx.p.blocks.size) {
            // terminal: evaluate payoffs
            val pay = evalPayoffs(ctx, state)
            addTerminal(parent, pay)
            return
        }

        val block = ctx.p.blocks[blockIdx]
        // Sequentialize moves but keep infosets from pre-state state (snapshot)
        val seqMoves = block.moves // preserve order as given

        // We expand a small sequence: for each move, define a decision node (if it has branching)
        expandMoveSeq(ctx, parent, seqMoves, 0, state.clone()) { stateAfter ->
            // After finishing the block, continue to next block
            expandBlocks(ctx, parent = stateAfter.nodePlaceholder ?: parent, blockIdx + 1, stateAfter.state)
        }
    }

    /** A small frame to pass both state & “attach point”. */
    private data class SeqFrame(val state: State, val nodePlaceholder: Node?)

    private fun expandMoveSeq(
        ctx: Ctx,
        attachTo: Node,
        moves: List<Move>,
        idx: Int,
        state: State,
        k: (SeqFrame) -> Unit
    ) {
        if (idx >= moves.size) {
            k(SeqFrame(state, attachTo))
            return
        }
        val m = moves[idx]

        // Determine action tuples (cartesian of params); if empty, elide node.
        val choices = actionTuples(ctx, m)
        val preSnapshot = state.clone() // infoset must be derived from pre-state

        if (choices.isEmpty()) {
            // e.g., REVEAL-only move or JOIN with no params: enforce guard & constraints
            if (!evalBool(ctx, m.guard, preSnapshot, m)) {
                // Illegal; prune this entire branch by not calling k
                return
            }
            // Apply deterministic effects (reveals)
            val state2 = state.clone()
            applyEffectsDeterministic(ctx, m, state2)
            expandMoveSeq(ctx, attachTo, moves, idx + 1, state2, k)
            return
        }

        // Decision node (or chance)
        val node = Node.Decision(
            player = m.by,
            infoKey = if (m.by == Role.Chance) null else infoKeyForMove(ctx, m, preSnapshot)
        )
        addChild(ctx, attachTo, node) // tie into tree

        // Emit edges
        when (m.kind) {
            MoveKind.CHANCE -> {
                val weights = chanceWeights(ctx, m, choices)
                for ((tuple, w) in choices.zip(weights)) {
                    val state2 = state.clone()
                    if (!evalBool(ctx, m.guard, preSnapshot, m)) continue
                    applyChoice(m, tuple, state2)
                    node.actions += ActionEdge(label = labelOf(tuple), prob = w, child = Node.Root)
                    // Continue the sequence under this edge
                    expandMoveSeq(ctx, node.actions.last().child, moves, idx + 1, state2, k)
                }
            }

            MoveKind.JOIN, MoveKind.SUBMIT -> {
                for (tuple in choices) {
                    val state2 = state.clone()
                    if (!evalBool(ctx, m.guard, preSnapshot, m)) continue
                    applyChoice(m, tuple, state2)
                    node.actions += ActionEdge(label = labelOf(tuple), prob = null, child = Node.Root)
                    expandMoveSeq(ctx, node.actions.last().child, moves, idx + 1, state2, k)
                }
            }

            MoveKind.REVEAL -> {
                // Should have been elided earlier (no branching); keep for safety
                val state2 = state.clone()
                if (!evalBool(ctx, m.guard, preSnapshot, m)) return
                applyEffectsDeterministic(ctx, m, state2)
                node.actions += ActionEdge(label = "ok", prob = Rational(1), child = Node.Root)
                expandMoveSeq(ctx, node.actions.last().child, moves, idx + 1, state2, k)
            }
        }
    }

    private fun addTerminal(parent: Node, payoffs: Array<Rational>) {
        when (parent) {
            is Node.Decision -> parent.actions += ActionEdge(label = "∅", prob = null, child = Node.Terminal(payoffs))
            is Node.Root -> error("Internal: terminal cannot attach to Root without a decision")
            is Node.Terminal -> error("Internal: double terminal")
        }
    }

    private fun addChild(ctx: Ctx, parent: Node, child: Node.Decision) {
        when (parent) {
            is Node.Root -> ctx.topLevel += child       // <— keep the root child
            is Node.Decision -> parent.actions += ActionEdge(label = "∅", prob = null, child = child)
            is Node.Terminal -> error("Internal: cannot add child to terminal")
        }
    }

    // ---------- Domains & choices ----------

    private fun actionTuples(ctx: Ctx, m: Move): List<ChoiceTuple> {
        if (m.params.isEmpty()) return emptyList()
        // REVEAL: not a choice — must match earlier commit; return empty (elide node)
        if (m.kind == MoveKind.REVEAL) return emptyList()

        // Cartesian product of finite domains
        val domains: List<List<ConstG>> = m.params.map { finiteDomain(ctx, it.type) }
        require(domains.all { it.isNotEmpty() }) { "Empty domain in move ${m.id}" }
        val names = m.params.map { it.name }
        val choices = mutableListOf<ChoiceTuple>()
        cartesian(domains) { tuple ->
            choices += names.zip(tuple)
        }
        return choices
    }

    private fun finiteDomain(ctx: Ctx, t: Type): List<ConstG> = ctx.dom.getOrPut(t) {
        when (t) {
            Type.BoolType -> listOf(ConstG.BoolV(false), ConstG.BoolV(true))
            is Type.Range -> (t.lo
                    ..t.hi
                    )
                .map { ConstG.IntV(it) }

            is Type.Subset -> t.values.map { ConstG.IntV(it) }
            is Type.Enum -> t.values.map { ConstG.EnumV(it) }
            is Type.Hidden -> finiteDomain(ctx, t.inner) // choice space = inner
            is Type.Opt -> finiteDomain(ctx, t.inner) + listOf() // undefined is *not* a separate action here
            Type.IntType -> error("Unbounded Int cannot be enumerated in EFG; use Range/Subset")
        }
    }

    private fun cartesian(domains: List<List<ConstG>>, k: (List<ConstG>) -> Unit) {
        val cur = ArrayList<ConstG>(domains.size)
        fun go(i: Int) {
            if (i == domains.size) {
                k(cur.toList()); return
            }
            for (v in domains[i]) {
                cur.add(v); go(i + 1); cur.removeAt(cur.lastIndex)
            }
        }
        go(0)
    }

    private fun labelOf(tuple: ChoiceTuple): String =
        tuple.joinToString(separator = ",") { (n, v) -> "$n=$v" }

    private fun chanceWeights(ctx: Ctx, m: Move, choices: List<ChoiceTuple>): List<Rational> {
        val weights = ctx.chanceWeights[m.id]
        return if (weights == null) {
            val p = Rational(1, choices.size)
            List(choices.size) { p }
        } else {
            choices.map { tuple ->
                val only: ConstG = tuple.single().second           // key is ConstG
                weights[only] ?: error("Missing weight for $only in chance ${m.id}")
            }
        }
    }

    // ---------- Effects ----------

    private fun applyChoice(m: Move, tuple: ChoiceTuple, state: State) {
        when (m.kind) {
            MoveKind.JOIN, MoveKind.SUBMIT, MoveKind.CHANCE -> {
                for ((param, value) in tuple) {
                    val key = m.id to param
                    val ty = m.params.first { it.name == param }.type
                    if (ty is Type.Hidden) {
                        // record commit (not public), remember owner secret
                        state.commits += key
                        state.ownerSecrets[key] = value
                    } else {
                        state.publicVals[key] = value
                    }
                }
            }

            MoveKind.REVEAL -> error("REVEAL should be deterministic")
        }
    }

    private fun applyEffectsDeterministic(ctx: Ctx, m: Move, state: State) {
        check(m.kind == MoveKind.REVEAL)
        // Reveal each param: pull from owner's secret; make public and mark revealed
        m.params.forEach { p ->
            val key = m.id to p.name
            when (p.type) {
                is Type.Hidden -> {
                    // The commit belongs to *some prior move*; match by (MoveId,param) name.
                    // Assume REVEAL move reuses same id/name pairs as commit producer, or name that we can match.
                    // Simplest: require a prior commit with same param name; if multiple, use the last by same role.
                    val producerKey = findCommittedKeyForReveal(ctx, m, p.name, state)
                    val v = state.ownerSecrets[producerKey] ?: error("No secret for $producerKey at reveal")
                    state.publicVals[producerKey] = v
                    state.revealed += producerKey
                }

                else -> {
                    // public reveal — just copy public (rare)
                    state.publicVals[key] = state.publicVals[key] ?: error("Reveal refers to missing public $key")
                }
            }
        }
    }

    private fun findCommittedKeyForReveal(ctx: Ctx, revealMove: Move, pname: String, state: State): Pair<MoveId, String> {
        // Heuristic: last commit by same role with that parameter name before this block.
        val revealBlock = ctx.moveIndex.getValue(revealMove.id)
        val candidates = ctx.p.blocks.take(revealBlock + 1)
            .flatMap { it.moves }
            .filter { it.by == revealMove.by }
            .flatMap { m ->
                m.params.filter { it.name == pname && it.type is Type.Hidden }.map { m.id to pname }
            }
            .filter { it in state.commits }
        require(candidates.isNotEmpty()) { "No committed $pname to reveal for ${revealMove.id}" }
        return candidates.last()
    }

    // ---------- Infosets ----------

    private fun infoKeyForMove(ctx: Ctx, m: Move, pre: State): InfoKey {
        // Signature = all public/revealed (move,param)->value pairs from *prior* blocks,
        // plus this role's own secrets from any earlier commits.
        val sb = StringBuilder()
        sb.append("pub:[")
        pre.publicVals.entries.sortedBy { it.key.first.s + "#" + it.key.second }.forEach {
            sb.append(it.key.first.s).append('.').append(it.key.second).append('=').append(it.value).append(';')
        }
        sb.append("];own:[")
        pre.ownerSecrets.filterKeys { (mid, _) ->
            // commits by this role prior to this move's block
            val prodBlock = ctx.moveIndex[mid] ?: -1
            val thisBlock = ctx.moveIndex[m.id] ?: Int.MAX_VALUE
            prodBlock < thisBlock && ctx.p.blocks[prodBlock].moves.any { it.by == m.by }
        }.entries.sortedBy { it.key.first.s + "#" + it.key.second }.forEach {
            sb.append(it.key.first.s).append('.').append(it.key.second).append('=').append(it.value).append(';')
        }
        sb.append("]")
        return InfoKey(m.by, sb.toString())
    }

    // ---------- Guards / Payoffs ----------

    private fun evalBool(ctx: Ctx, e: Expr, pre: State, m: Move): Boolean =
        when (val v = evalExpr(ctx, e, pre)) {
            is Val.B -> v.v
            else -> error("Guard did not evaluate to boolean at ${m.id}")
        }

    private sealed class Val {
        data class I(val v: Int) : Val()
        data class B(val v: Boolean) : Val()
        data class E(val tag: String) : Val()
    }

    private fun evalPayoffs(ctx: Ctx, state: State): Array<Rational> {
        val players = ctx.p.roles.filter { it != Role.Chance }
        return Array(players.size) { i ->
            val role = players[i]
            val e = ctx.p.payoffs.getValue(role)
            when (val v = evalExpr(ctx, e, state)) {
                is Val.I -> Rational(v.v)
                else -> error("Payoff must be integer")
            }
        }
    }

    private fun evalExpr(ctx: Ctx, e: Expr, state: State): Val = when (e) {
        is Expr.IntLit -> Val.I(e.v)
        is Expr.Bool -> Val.B(e.v)
        is Expr.Field -> {
            val key = e.move to e.param
            val pub = state.publicVals[key]
            if (pub != null) constToVal(pub)
            else error("Undefined field ${e.move}.${e.param} (not public/revealed yet)")
        }

        is Expr.IsDef -> {
            val key = e.of.move to e.of.param
            Val.B(state.publicVals.containsKey(key))
        }

        is Expr.IsUndef -> {
            val key = e.of.move to e.of.param
            Val.B(!state.publicVals.containsKey(key))
        }

        is Expr.Add -> (evalExpr(ctx, e.l, state) as Val.I).let { l ->
            val r = evalExpr(ctx, e.r, state) as Val.I
            Val.I(l.v + r.v)
        }

        is Expr.Sub -> (evalExpr(ctx, e.l, state) as Val.I).let { l ->
            val r = evalExpr(ctx, e.r, state) as Val.I
            Val.I(l.v - r.v)
        }

        is Expr.Mul -> (evalExpr(ctx, e.l, state) as Val.I).let { l ->
            val r = evalExpr(ctx, e.r, state) as Val.I
            Val.I(l.v * r.v)
        }

        is Expr.Div -> (evalExpr(ctx, e.l, state) as Val.I).let { l ->
            val r = evalExpr(ctx, e.r, state) as Val.I
            require(r.v != 0) { "Division by zero" }
            Val.I(l.v / r.v)
        }

        is Expr.Eq -> Val.B(equalVals(evalExpr(ctx, e.l, state), evalExpr(ctx, e.r, state)))
        is Expr.Ne -> Val.B(!equalVals(evalExpr(ctx, e.l, state), evalExpr(ctx, e.r, state)))
        is Expr.Lt -> cmp(ctx, e, state) { a, b -> a < b }
        is Expr.Le -> cmp(ctx, e, state) { a, b -> a <= b }
        is Expr.Gt -> cmp(ctx, e, state) { a, b -> a > b }
        is Expr.Ge -> cmp(ctx, e, state) { a, b -> a >= b }
        is Expr.And -> Val.B(
            (evalExpr(ctx, e.l, state) as Val.B).v && (evalExpr(
                ctx,
                e.r,
                state
            ) as Val.B).v
        )

        is Expr.Or -> Val.B(
            (evalExpr(ctx, e.l, state) as Val.B).v || (evalExpr(
                ctx,
                e.r,
                state
            ) as Val.B).v
        )

        is Expr.Not -> Val.B(!(evalExpr(ctx, e.x, state) as Val.B).v)
        is Expr.Ite -> if ((evalExpr(ctx, e.c, state) as Val.B).v) evalExpr(
            ctx,
            e.t,
            state
        ) else evalExpr(ctx, e.e, state)
    }

    private fun cmp(ctx: Ctx, e: Expr, state: State, op: (Int, Int) -> Boolean): Val.B {
        val (lExpr, rExpr) = when (e) {
            is Expr.Lt -> e.l to e.r
            is Expr.Le -> e.l to e.r
            is Expr.Gt -> e.l to e.r
            is Expr.Ge -> e.l to e.r
            else -> error("cmp expects a relational expression")
        }
        val lv = evalExpr(ctx, lExpr, state) as Val.I
        val rv = evalExpr(ctx, rExpr, state) as Val.I
        return Val.B(op(lv.v, rv.v))
    }


    private fun equalVals(a: Val, b: Val): Boolean = when {
        a is Val.I && b is Val.I -> a.v == b.v
        a is Val.B && b is Val.B -> a.v == b.v
        a is Val.E && b is Val.E -> a.tag == b.tag
        else -> false
    }

    private fun constToVal(c: ConstG): Val = when (c) {
        is ConstG.IntV -> Val.I(c.v)
        is ConstG.BoolV -> Val.B(c.v)
        is ConstG.EnumV -> Val.E(c.tag)
    }

    // ---------- Printer (Gambit .efg) ----------

    private class Printer(private val out: StringBuilder, private val players: List<String>) {
        // Node numbering and infoset numbering per player
        private var nextNodeId = 1
        private val infoIds = HashMap<InfoKey, Int>()
        private val chanceName = "Chance"

        fun emit(root: Node, ctx: Ctx) {
                // Depth-first traversal assigning node & infoset ids as we go.
                when (root) {
                    is Node.Root -> {
                        // Root must have been connected to a child decision via addChild; print children directly.
                        // If tree is a single terminal, emit a degenerate 1-node game:
                        out.append("") // nothing else to do; children are emitted during recursion below
                    }

                    else -> Unit
                }
                // We need to emit starting from a synthetic root; for simplicity, we gather top-level children
                // by expanding again but collecting at print time. We therefore define a nested walker:
                fun walk(n: Node) {
                    when (n) {
                        is Node.Decision -> {
                            val nodeId = nextNodeId++
                            if (n.player == Role.Chance) {
                                // c node: "c <nodeId>  <numActions>  <p1> <p2> ...  \"label\""
                                out.append("c $nodeId ${n.actions.size}")
                                n.actions.forEach { a ->
                                    out.append(' ').append(requireNotNull(a.prob) { "Chance edge needs prob" })
                                }
                                out.append(" \"$chanceName\"").append('\n')
                            } else {
                                val playerIndex = players.indexOf(n.player.name) + 1
                                val info = n.infoKey ?: error("Missing infoset for player ${n.player.name}")
                                val infoId = infoIds.getOrPut(info) { infoIds.size + 1 }
                                // p node: "p <nodeId>  <playerIndex>  <infosetId>  <numActions> \"label\"  \"a1\" ... "
                                out.append("p $nodeId $playerIndex $infoId ${n.actions.size} \"${n.player.name}\"")
                                n.actions.forEach { a -> out.append(" \"").append(a.label).append('"') }
                                out.append('\n')
                            }
                            // Children
                            n.actions.forEach { edge -> walk(edge.child) }
                        }

                        is Node.Terminal -> {
                            // t node: "t \"label\" <u1> <u2> ..."
                            out.append("t \"z\"")
                            n.payoffs.forEach { u -> out.append(' ').append(u) }
                            out.append('\n')
                        }

                        is Node.Root -> { /* nothing */
                        }
                    }
                }
            ctx.topLevel.forEach { top -> walk(top) }
            // Re-expand starting at synthetic root: attach children via a faux decision
            // We can traverse from protocol again; but we already created nodes in expand phase
            // that are linked via ActionEdge.child. So we need a "starting decision" to walk from.
            // Solution: collect top-level decisions reachable from Root among edges we created,
            // by scanning a small union from context… but we don't store them. Instead, we
            // build the tree with a single starting block move; so we call walk on each child
            // reachable by exploring during generation. Here, we assume expand added at least one decision;
            // a more robust impl would store the first-level decisions. For simplicity, users will call emit
            // right after generate, and generation attached nodes in order. (If needed, refactor to keep a root list.)
        }
    }
}

fun generateExtensiveFormGame(ir: ProgramIR) = GambitEfgBackend.generate(ir)
