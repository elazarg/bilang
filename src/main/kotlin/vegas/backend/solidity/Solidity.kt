package vegas.backend.solidity

import vegas.frontend.Role
import vegas.ir.Expr
import vegas.ir.Move
import vegas.ir.MoveId
import vegas.ir.MoveKind
import vegas.ir.Param
import vegas.ir.ProgramIR
import vegas.ir.Type

data class SolcConfig(
    val pragma: String = "pragma solidity ^0.8.24;",
    val contractNamePrefix: String = "",
    val coordinatorAddress: String? = null, // if set, only this addr may call CHANCE moves
    val exposeGetters: Boolean = true,
    val revertOnUnusedNextPhase: Boolean = false, // if true, nextPhase() reverts when not all-done
    val numericModel: NumericModel = NumericModel.Int256Checked
)

enum class NumericModel { Int256Checked }

private inline fun StringBuilder.indent(block: StringBuilder.() -> Unit) {
    this.block()
}

object SolidityBackend {
    fun generate(p: ProgramIR, cfg: SolcConfig = SolcConfig()): String {
        checkWellFormedForSolidity(p)
        val sb = StringBuilder()

        val fieldT: Map<Pair<MoveId, String>, Type> = buildMap {
            p.blocks.forEach { b ->
                b.moves.forEach { m ->
                    m.params.forEach { pa -> put(m.id to pa.name, pa.type) }
                }
            }
        }
        sb.appendLine(cfg.pragma).appendLine()
        sb.appendLine("// Auto-generated from Vegas IR. Do not edit by hand.")
        sb.appendLine("contract ${cfg.contractNamePrefix}${p.name} {")
        sb.indent {
            // Roles → addresses
            emitRoles(p, this)

            // Phase (“block”) management
            emitPhaseState(p, this)

            // Storage for each move/param (commit/open/value/done bits)
            emitStorage(p, this)

            // Constructor
            emitCtor(cfg, this)

            // Helpers
            emitHashHelpers(this)
            emitVisibilityHelpers(p, this)

            // Move functions
            p.blocks.forEachIndexed { bi, b ->
                b.moves.forEach { m ->
                    emitGuardFunction(m, m.guard, this, fieldT)
                    emitMoveFunction(cfg, bi, p, m, this, fieldT)
                }
            }

            // Phase advancement
            emitNextPhase(p, cfg, this)

            // Payoff computation & withdraw
            emitPayoffArea(p, this, fieldT)
        }

        sb.appendLine("}")
        return sb.toString()
    }
    private fun moveIndexMap(p: ProgramIR): Map<MoveId, Int> =
        p.blocks.flatMapIndexed { idx, b -> b.moves.map { it.id to idx } }.toMap()

    private fun referencedMoves(e: Expr, acc: MutableSet<MoveId> = linkedSetOf()): Set<MoveId> {
        when (e) {
            is Expr.Field       -> acc += e.move
            is Expr.IsDef       -> acc += e.of.move
            is Expr.IsUndef     -> acc += e.of.move
            is Expr.Add         -> { referencedMoves(e.l, acc); referencedMoves(e.r, acc) }
            is Expr.Sub         -> { referencedMoves(e.l, acc); referencedMoves(e.r, acc) }
            is Expr.Mul         -> { referencedMoves(e.l, acc); referencedMoves(e.r, acc) }
            is Expr.Div         -> { referencedMoves(e.l, acc); referencedMoves(e.r, acc) }
            is Expr.Eq          -> { referencedMoves(e.l, acc); referencedMoves(e.r, acc) }
            is Expr.Ne          -> { referencedMoves(e.l, acc); referencedMoves(e.r, acc) }
            is Expr.Lt          -> { referencedMoves(e.l, acc); referencedMoves(e.r, acc) }
            is Expr.Le          -> { referencedMoves(e.l, acc); referencedMoves(e.r, acc) }
            is Expr.Gt          -> { referencedMoves(e.l, acc); referencedMoves(e.r, acc) }
            is Expr.Ge          -> { referencedMoves(e.l, acc); referencedMoves(e.r, acc) }
            is Expr.And         -> { referencedMoves(e.l, acc); referencedMoves(e.r, acc) }
            is Expr.Or          -> { referencedMoves(e.l, acc); referencedMoves(e.r, acc) }
            is Expr.Not         -> referencedMoves(e.x, acc)
            is Expr.Ite         -> { referencedMoves(e.c, acc); referencedMoves(e.t, acc); referencedMoves(e.e, acc) }
            is Expr.IntLit, is Expr.Bool -> {}
        }
        return acc
    }

    /** Split guard into:
     *  - preGuard: safe to check in this block (only prior moves referenced)
     *  - deferred: original guard, to be enforced at finalize (when all refs exist)
     * For simplicity we take all-or-nothing: if any future ref exists, defer whole guard.
     */
    private fun splitGuardForPhase(guard: Expr, currentBlock: Int, idxByMove: Map<MoveId, Int>): Pair<Expr, Expr?> {
        val anyFuture = referencedMoves(guard).any { mid -> idxByMove.getValue(mid) > currentBlock }
        return if (!anyFuture) guard to null else Expr.Bool(true) to guard
    }
    private fun emitGuardFunction(m: Move, fullGuard: Expr, out: Appendable, fieldT: Map<Pair<MoveId,String>, Type>) {
        val fn = "guard_full_${sanitize(m.id.s)}"
        val body = emitExpr(fullGuard, publicOnly = true, fieldT)
        out.appendLine("    function $fn() public view returns (bool) {")
        out.appendLine("        return ($body);")
        out.appendLine("    }")
        out.appendLine()
    }

    // ---------- WF preflight specific to Solidity ----------

    private fun checkWellFormedForSolidity(p: ProgramIR) {
        // Guards only read prior-block public/revealed: IR WfChecks should enforce;
        // here we just sanity-check there are no forward refs in Expr.Field.
        val indexByMove = p.blocks.flatMapIndexed { idx, b -> b.moves.map { it.id to idx } }.toMap()
        fun checkExpr(e: Expr, currentBlock: Int) {
            when (e) {
                is Expr.Field -> {
                    val producerBlock = indexByMove[e.move] ?: error("Unknown move ${e.move}")
                }

                is Expr.Add -> {
                    checkExpr(e.l, currentBlock); checkExpr(e.r, currentBlock)
                }

                is Expr.Sub -> {
                    checkExpr(e.l, currentBlock); checkExpr(e.r, currentBlock)
                }

                is Expr.Mul -> {
                    checkExpr(e.l, currentBlock); checkExpr(e.r, currentBlock)
                }

                is Expr.Div -> {
                    checkExpr(e.l, currentBlock); checkExpr(e.r, currentBlock)
                }

                is Expr.Eq -> {
                    checkExpr(e.l, currentBlock); checkExpr(e.r, currentBlock)
                }

                is Expr.Ne -> {
                    checkExpr(e.l, currentBlock); checkExpr(e.r, currentBlock)
                }

                is Expr.Lt -> {
                    checkExpr(e.l, currentBlock); checkExpr(e.r, currentBlock)
                }

                is Expr.Le -> {
                    checkExpr(e.l, currentBlock); checkExpr(e.r, currentBlock)
                }

                is Expr.Gt -> {
                    checkExpr(e.l, currentBlock); checkExpr(e.r, currentBlock)
                }

                is Expr.Ge -> {
                    checkExpr(e.l, currentBlock); checkExpr(e.r, currentBlock)
                }

                is Expr.And -> {
                    checkExpr(e.l, currentBlock); checkExpr(e.r, currentBlock)
                }

                is Expr.Or -> {
                    checkExpr(e.l, currentBlock); checkExpr(e.r, currentBlock)
                }

                is Expr.Not -> checkExpr(e.x, currentBlock)
                is Expr.Ite -> {
                    checkExpr(e.c, currentBlock); checkExpr(e.t, currentBlock); checkExpr(e.e, currentBlock)
                }

                is Expr.IsDef -> checkExpr(e.of, currentBlock)
                is Expr.IsUndef -> checkExpr(e.of, currentBlock)
                is Expr.IntLit, is Expr.Bool -> {}
            }
        }
        // Check guards per block, and payoffs at terminal
        p.blocks.forEachIndexed { k, b ->
            b.moves.forEach { checkExpr(it.guard, k) }
        }
        p.payoffs.values.forEach { checkExpr(it, p.blocks.size) }
    }

    // ---------- Role management ----------

    private fun emitRoles(p: ProgramIR, out: Appendable) {
        out.appendLine("    // Role addresses (bound on first JOIN by that role)")
        p.roles.forEach { r ->
            out.appendLine("    address public ${roleVar(r)};")
        }
        out.appendLine()
    }

    private fun roleVar(r: Role) = "role_${sanitize(r.name)}"

    // ---------- Phase state ----------

    private fun emitPhaseState(p: ProgramIR, out: Appendable) {
        out.appendLine("    // Phases correspond to IR blocks")
        out.appendLine("    uint256 public phase; // starts at 0")
        out.appendLine("    uint256 constant PHASES = ${p.blocks.size};")
        out.appendLine()
    }

    // ---------- Storage layout ----------

    private fun emitStorage(p: ProgramIR, out: Appendable) {
        // For each move param, produce structs/state
        p.blocks.forEach { b ->
            b.moves.forEach { m ->
                m.params.forEach { param ->
                    val base = storageBase(m, param.name)
                    when (param.type) {
                        is Type.Hidden -> {
                            out.appendLine("    // Hidden commit for ${m.id}.${param.name}")
                            out.appendLine("    struct ${base}Commit { bytes32 commit; bool done; }")
                            out.appendLine("    ${base}Commit public ${base}_commit;")
                            out.appendLine("    // Reveal record (becomes public)")
                            val solT = solType(param.type.inner)
                            out.appendLine("    struct ${base}Open { $solT value; bytes32 salt; bool revealed; }")
                            out.appendLine("    ${base}Open public ${base}_open;")
                        }

                        else -> {
                            val solT = solType(param.type)
                            out.appendLine("    // Public param for ${m.id}.${param.name}")
                            out.appendLine("    struct ${base}Val { $solT value; bool done; }")
                            out.appendLine("    ${base}Val public ${base};")
                        }
                    }
                }
            }
        }
        out.appendLine()
        out.appendLine("    // Payoff storage (signed int); settlement is out of scope")
        out.appendLine("    mapping(address => int256) public payoff;")
        out.appendLine("    bool public finalized;")
        out.appendLine()
    }

    private fun storageBase(m: Move, param: String) =
        "S_${sanitize(m.id.s)}_${sanitize(param)}"

    private fun sanitize(s: String): String =
        s.replace(Regex("[^A-Za-z0-9_]"), "_")

    // ---------- Constructor ----------

    private fun emitCtor(cfg: SolcConfig, out: Appendable) {
        out.appendLine("    constructor() {")
        out.appendLine("        phase = 0;")
        out.appendLine("    }")
        out.appendLine()
        if (cfg.exposeGetters) {
            out.appendLine("    function currentPhase() external view returns(uint256){ return phase; }")
            out.appendLine()
        }
    }

    // ---------- Helpers ----------

    private fun emitHashHelpers(out: Appendable) {
        out.appendLine("    // Commitment helper")
        out.appendLine("    function _commit(bytes memory data) internal pure returns (bytes32) {")
        out.appendLine("        return keccak256(data);")
        out.appendLine("    }")
        out.appendLine()
    }

    private fun emitVisibilityHelpers(p: ProgramIR, out: Appendable) {
        out.appendLine("    // Definedness helpers (public visibility only)")
        p.blocks.forEach { b ->
            b.moves.forEach { m ->
                m.params.forEach { param ->
                    val base = storageBase(m, param.name)
                    val fn = "isDefined_${base}"
                    when (param.type) {
                        is Type.Hidden -> {
                            out.appendLine("    function $fn() public view returns (bool) { return ${base}_open.revealed; }")
                        }

                        else -> {
                            out.appendLine("    function $fn() public view returns (bool) { return ${base}.done; }")
                        }
                    }
                }
            }
        }
        out.appendLine()
    }

    // ---------- Move functions ----------

    private fun emitMoveFunction(
        cfg: SolcConfig,
        blockIndex: Int,
        p: ProgramIR,
        m: Move,
        out: Appendable,
        fieldT: Map<Pair<MoveId, String>, Type>
    ) {
        val fnName = "move_${sanitize(m.id.s)}"
        val phaseReq = "require(phase == $blockIndex, \"wrong phase\");"
        val roleGate = when {
            m.by == Role.Chance -> null // handled separately for CHANCE
            else -> "require(${roleVar(m.by)} == address(0) || ${roleVar(m.by)} == msg.sender, \"role mismatch\");"
        }

        when (m.kind) {
            MoveKind.JOIN, MoveKind.SUBMIT -> {
                // parameters: non-hidden -> value; hidden -> bytes32 commit
                val inputs = m.params.joinToString(", ") { paramInputDecl(it) }
                out.appendLine("    function $fnName($inputs) external {")
                out.appendLine("        $phaseReq")
                if (roleGate != null) out.appendLine("        $roleGate")
                // Bind role address if first JOIN by that role
                if (m.kind == MoveKind.JOIN) {
                    out.appendLine("        if (${roleVar(m.by)} == address(0)) { ${roleVar(m.by)} = msg.sender; }")
                }
                val idxByMove = moveIndexMap(p)
                val (preGuardExpr, deferredGuard) = splitGuardForPhase(m.guard, blockIndex, idxByMove)
                val guardExprSol = emitExpr(preGuardExpr, true, fieldT)
                out.appendLine("        require($guardExprSol, \"guard failed (pre)\");")

                // Store params
                m.params.forEach { param ->
                    val base = storageBase(m, param.name)
                    when (param.type) {
                        is Type.Hidden -> {
                            out.appendLine("        require(!${base}_commit.done, \"already committed\");")
                            out.appendLine("       ${base}_commit.commit = ${param.name}_commit;")
                            out.appendLine("        ${base}_commit.done = true;")
                        }

                        else -> {
                            out.appendLine("        require(!${base}.done, \"already set\");")
                            // Range/Subset/Enum checks
                            emitTypeGuards(param, out)
                            out.appendLine("        ${base}.value = ${param.name};")
                            out.appendLine("        ${base}.done = true;")
                        }
                    }
                }

                out.appendLine("    }")
                out.appendLine()
            }

            MoveKind.REVEAL -> {
                // For each revealed param: value + salt; we verify against prior commit
                val inputs = m.params.joinToString(", ") { param ->
                    when (param.type) {
                        is Type.Hidden -> {
                            // Reveal carries the opened inner type + salt
                            val inner = param.type.inner
                            "${solType(inner)} ${param.name}_val, bytes32 ${param.name}_salt"
                        }

                        else -> "${solType(param.type)} ${param.name}" // public reveal (rare), keep general
                    }
                }
                out.appendLine("    function $fnName($inputs) external {")
                out.appendLine("        $phaseReq")
                val rg =
                    if (m.by != Role.Chance) "require(${roleVar(m.by)} == msg.sender, \"reveal by owner only\");" else null
                if (rg != null) out.appendLine("        $rg")

                val guardExpr = emitExpr(m.guard, true, fieldT)
                out.appendLine("        require($guardExpr, \"guard failed\");")

                m.params.forEach { param ->
                    val base = storageBase(m, param.name)
                    when (param.type) {
                        is Type.Hidden -> {
                            val inner = param.type.inner
                            out.appendLine("        require(${base}_commit.done, \"no prior commit\");")
                            out.appendLine("        require(!${base}_open.revealed, \"already revealed\");")
                            // Range/Subset/Enum checks on opened value
                            emitTypeGuards(Param("${param.name}_val", inner), out)
                            out.appendLine("        bytes32 com = _commit(abi.encode(${param.name}_val, ${param.name}_salt));")
                            out.appendLine("        require(com == ${base}_commit.commit, \"commit mismatch\");")
                            out.appendLine("        ${base}_open.value = ${param.name}_val;")
                            out.appendLine("        ${base}_open.salt = ${param.name}_salt;")
                            out.appendLine("        ${base}_open.revealed = true;")
                        }

                        else -> {
                            out.appendLine("        require(!${base}.done, \"already set\");")
                            emitTypeGuards(param, out)
                            out.appendLine("        ${base}.value = ${param.name};")
                            out.appendLine("        ${base}.done = true;")
                        }
                    }
                }

                out.appendLine("    }")
                out.appendLine()
            }

            MoveKind.CHANCE -> {
                // Policy: a designated coordinator sets chance outcomes.
                val inputs = m.params.joinToString(", ") { paramInputDeclForChance(it) }
                out.appendLine("    function $fnName($inputs) external {")
                out.appendLine("        $phaseReq")
                if (cfg.coordinatorAddress != null) {
                    out.appendLine("        require(msg.sender == ${cfg.coordinatorAddress}, \"only coordinator\");")
                } else {
                    out.appendLine("        // WARNING: no coordinator configured; anyone may call this chance move.")
                }
                val idxByMove = moveIndexMap(p)
                val (preGuardExpr, deferredGuard) = splitGuardForPhase(m.guard, blockIndex, idxByMove)
                val guardExprSol = emitExpr(preGuardExpr, true, fieldT)
                out.appendLine("        require($guardExprSol, \"guard failed (pre)\");")

                m.params.forEach { param ->
                    val base = storageBase(m, param.name)
                    when (param.type) {
                        is Type.Hidden -> {
                            out.appendLine("        require(!${base}_commit.done, \"already committed\");")
                            out.appendLine("        ${base}_commit.commit = _commit(abi.encode(${param.name}));")
                            out.appendLine("        ${base}_commit.done = true;")
                        }

                        else -> {
                            out.appendLine("        require(!${base}.done, \"already set\");")
                            emitTypeGuards(param, out)
                            out.appendLine("        ${base}.value = ${param.name};")
                            out.appendLine("        ${base}.done = true;")
                        }
                    }
                }
                out.appendLine("    }")
                out.appendLine()
            }
        }
    }

    private fun paramInputDecl(param: Param): String =
        when (param.type) {
            is Type.Hidden -> "bytes32 ${param.name}_commit"
            else -> "${solType(param.type)} ${param.name}"
        }

    private fun paramInputDeclForChance(param: Param): String =
        when (param.type) {
            is Type.Hidden -> "bytes32 ${param.name}_commit"
            else -> "${solType(param.type)} ${param.name}"
        }

    // Additional validation for Range / Subset / Enum.
    private fun emitTypeGuards(param: Param, out: Appendable) {
        when (param.type) {
            is Type.Range -> {
                val t = param.type
                out.appendLine("        require(${param.name} >= ${t.lo} && ${param.name} <= ${t.hi}, \"out of range\");")
            }

            is Type.Subset -> {
                val s = param.type.values
                val cond = s.joinToString(" || ") { "${param.name} == $it" }
                out.appendLine("        require($cond, \"not in subset\");")
            }

            is Type.Enum -> {
                // encode as uint256; values checked against length-1
                val e = param.type
                val hi = e.values.size - 1
                out.appendLine("        require(${param.name} <= $hi, \"enum tag out of range\");")
            }

            is Type.Hidden, is Type.Opt, Type.IntType, Type.BoolType -> { /* no extra guard here */
            }
        }
    }

    private fun solType(t: Type): String = when (t) {
        Type.IntType -> "int256"
        Type.BoolType -> "bool"
        is Type.Range -> "int256"
        is Type.Subset -> "int256"
        is Type.Enum -> "uint256"
        is Type.Hidden -> error("Hidden has no direct Solidity type; use commit/reveal")
        is Type.Opt -> solType(t.inner) // value slot still uses inner type; definedness via .done
    }

    // ---------- Phase advancement ----------

    private fun emitNextPhase(p: ProgramIR, cfg: SolcConfig, out: Appendable) {
        out.appendLine("    function nextPhase() external {")
        out.appendLine("        require(phase < PHASES, \"already finished\");")
        out.appendLine("        if (_allMovesDoneInPhase(phase)) { phase += 1; }")
        if (cfg.revertOnUnusedNextPhase) {
            out.appendLine("        else { revert(\"moves missing\"); }")
        }
        out.appendLine("    }")
        out.appendLine()
        out.appendLine("    function _allMovesDoneInPhase(uint256 ph) internal view returns (bool) {")
        out.appendLine("        if (ph >= PHASES) return false;")
        out.appendLine("        bool ok = true;")
        p.blocks.forEachIndexed { idx, b ->
            out.appendLine("        if (ph == $idx) {")
            b.moves.forEach { m ->
                m.params.forEach { param ->
                    val base = storageBase(m, param.name)
                    when (param.type) {
                        is Type.Hidden -> out.appendLine("            ok = ok && (${base}_commit.done);")
                        else -> out.appendLine("            ok = ok && (${base}.done);")
                    }
                }
            }
            out.appendLine("        }")
        }
        out.appendLine("        return ok;")
        out.appendLine("    }")
        out.appendLine()
    }

    // ---------- Payoffs ----------

    private fun emitPayoffArea(p: ProgramIR, out: Appendable, fieldT: Map<Pair<MoveId, String>, Type>) {
        out.appendLine("    function finalizeAndComputePayoffs() external {")
        out.appendLine("        require(phase == PHASES, \"not finished\");")
        out.appendLine("        require(!finalized, \"already finalized\");")
        p.blocks.forEach { b ->
            b.moves.forEach { m ->
                val fn = "guard_full_${sanitize(m.id.s)}()"
                out.appendLine("        require($fn, \"deferred guard failed\");")
            }
        }
        // Evaluate payoff expressions per role
        p.payoffs.forEach { (role, expr) ->
            val sol = emitExpr(expr, true, fieldT)
            out.appendLine("        payoff[${roleAddress(role)}] = int256($sol);")
        }
        out.appendLine("        finalized = true;")
        out.appendLine("    }")
        out.appendLine()
        out.appendLine("    function payoffOf(address who) external view returns (int256) { return payoff[who]; }")
        out.appendLine()
    }

    private fun roleAddress(r: Role): String = when (r) {
        Role.Chance -> "address(0)" // no economic agent; harmless
        else -> roleVar(r)
    }

    // ---------- Expr emitter ----------

    /**
     * publicOnly=true means: Hidden fields are only readable via their revealed ".value".
     * IsDef/IsUndef map to .done (.revealed for hidden).
     */
    private fun emitExpr(e: Expr, publicOnly: Boolean, fieldT: Map<Pair<MoveId,String>, Type>): String = when (e) {
        is Expr.Field -> {
            val base = "S_${sanitize(e.move.s)}_${sanitize(e.param)}"
            when (fieldT[e.move to e.param]) {
                is Type.Hidden -> "({ require(${base}_open.revealed, \"hidden not revealed\"); ${base}_open.value; })"
                else           -> "(${base}.value)"
            }
        }
        is Expr.IsDef -> {
            val f = e.of; val base = "S_${sanitize(f.move.s)}_${sanitize(f.param)}"
            when (fieldT[f.move to f.param]) {
                is Type.Hidden -> "(${base}_open.revealed)"
                else           -> "(${base}.done)"
            }
        }
        is Expr.IsUndef -> {
            val f = e.of; val base = "S_${sanitize(f.move.s)}_${sanitize(f.param)}"
            when (fieldT[f.move to f.param]) {
                is Type.Hidden -> "(!${base}_open.revealed)"
                else           -> "(!${base}.done)"
            }
        }
        is Expr.IntLit -> e.v.toString()
        is Expr.Bool -> if (e.v) "true" else "false"

        is Expr.Add -> "(${emitExpr(e.l, publicOnly, fieldT)} + ${emitExpr(e.r, publicOnly, fieldT)})"
        is Expr.Sub -> "(${emitExpr(e.l, publicOnly, fieldT)} - ${emitExpr(e.r, publicOnly, fieldT)})"
        is Expr.Mul -> "(${emitExpr(e.l, publicOnly, fieldT)} * ${emitExpr(e.r, publicOnly, fieldT)})"
        is Expr.Div -> "(${emitExpr(e.l, publicOnly, fieldT)} / ${emitExpr(e.r, publicOnly, fieldT)})"
        is Expr.Eq -> "(${emitExpr(e.l, publicOnly, fieldT)} == ${emitExpr(e.r, publicOnly, fieldT)})"
        is Expr.Ne -> "(${emitExpr(e.l, publicOnly, fieldT)} != ${emitExpr(e.r, publicOnly, fieldT)})"
        is Expr.Lt -> "(${emitExpr(e.l, publicOnly, fieldT)} < ${emitExpr(e.r, publicOnly, fieldT)})"
        is Expr.Le -> "(${emitExpr(e.l, publicOnly, fieldT)} <= ${emitExpr(e.r, publicOnly, fieldT)})"
        is Expr.Gt -> "(${emitExpr(e.l, publicOnly, fieldT)} > ${emitExpr(e.r, publicOnly, fieldT)})"
        is Expr.Ge -> "(${emitExpr(e.l, publicOnly, fieldT)} >= ${emitExpr(e.r, publicOnly, fieldT)})"
        is Expr.And -> "(${emitExpr(e.l, publicOnly, fieldT)} && ${emitExpr(e.r, publicOnly, fieldT)})"
        is Expr.Or -> "(${emitExpr(e.l, publicOnly, fieldT)} || ${emitExpr(e.r, publicOnly, fieldT)})"
        is Expr.Not -> "(!${emitExpr(e.x, publicOnly, fieldT)})"
        is Expr.Ite -> "(${emitExpr(e.c, publicOnly, fieldT)} ? ${emitExpr(e.t, publicOnly, fieldT)} : ${emitExpr(e.e, publicOnly, fieldT)})"
    }
}

fun generateSolidity(ir: ProgramIR) = SolidityBackend.generate(ir)
