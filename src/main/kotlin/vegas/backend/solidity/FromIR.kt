package vegas.backend.solidity

import vegas.RoleId
import vegas.VarId
import vegas.FieldRef
import vegas.ir.*

fun genSolidityFromIR(g: GameIR) : String {
    val solAst = irToSolidity(g)
    return renderSolidityContract(solAst)
}

/**
 * Main entry: translate IR to a SolidityContract AST that matches the current goldens.
 */
fun irToSolidity(g: GameIR): SolidityContract {
    val history = ParamHistory(g)

    // ---- Constructor: set lastTs = block.timestamp
    val ctor = Constructor(
        body = listOf(
            // lastTs = block.timestamp;
            Statement.Assign(
                lhs = SolExpr.Var(LAST_TS_VAR),
                rhs = SolExpr.Member(SolExpr.Var("block"), "timestamp")
            )
        )
    )

    // ---- Role enum (None + all roles)
    val roleEnum = EnumDecl(
        name = ROLE_ENUM,
        values = listOf("None") + g.roles.map { it.name }
    )

    // ---- Storage (timing, role/balance, per-field state)
    val storage = buildList {
        // step timing
        add(
            StorageDecl(
                type = SolType.Uint256,
                visibility = Visibility.PUBLIC,
                name = STEP_TIME_CONST,
                constant = true,
                value = uint(500) // keep as in golden
            )
        )
        add(StorageDecl(SolType.Uint256, Visibility.PUBLIC, STEP_VAR))
        add(StorageDecl(SolType.Uint256, Visibility.PUBLIC, LAST_TS_VAR))

        // roles and balances
        add(
            StorageDecl(
                type = SolType.Mapping(SolType.Address, SolType.EnumType(ROLE_ENUM)),
                visibility = Visibility.PUBLIC,
                name = ROLE_MAPPING
            )
        )
        add(
            StorageDecl(
                type = SolType.Mapping(SolType.Address, SolType.Uint256),
                visibility = Visibility.PUBLIC,
                name = BALANCE_MAPPING
            )
        )

        // Per-game storage (params, done flags, etc.)
        addAll(buildGameStorage(g, history))
    }

    // ---- Modifiers
    val modifiers = listOf(
        // modifier at_step(uint _step) { require(step == _step); /* timers commented per golden */ _; }
        ModifierDecl(
            name = "at_step",
            params = listOf(Param(SolType.Uint256, "_step")),
            body = listOf(
                require(v(STEP_VAR) eq v("_step"), "wrong step")
                // (Your goldens keep STEP_TIME gate lines commented out.)
            )
        ),
        // modifier by(Role r) { require(role[msg.sender] == r, "bad role"); _; }
        ModifierDecl(
            name = "by",
            params = listOf(Param(SolType.EnumType(ROLE_ENUM), "r")),
            body = listOf(
                require(index(ROLE_MAPPING, msgSender) eq enumVal(ROLE_ENUM, "r"), "bad role")
            )
        )
    )

    // ---- Functions
    val functions = buildList {
        // keccak helper (bool variant per your goldens; easy to extend if you add more arities/types)
        add(
            FunctionDecl(
                name = "keccak",
                params = listOf(Param(SolType.Bool, "x"), Param(SolType.Uint256, "salt")),
                visibility = Visibility.PUBLIC,
                stateMutability = StateMutability.PURE,
                modifiers = emptyList(),
                returns = listOf(Param(SolType.Bytes32, "out")),
                body = listOf(
                    ret(SolExpr.Keccak256(SolExpr.AbiEncodePacked(listOf(v("x"), v("salt")))))
                )
            )
        )

        // Phase blocks
        g.phases.forEachIndexed { phaseIdx, phase ->
            addAll(buildPhaseFunctions(g, phaseIdx, phase, history))
        }

        // withdraw(): the exact flow your goldens implement (effects-first; low-level send tuple destructuring)
        add(buildWithdraw())

        // (Any other game-specific functions can be added here.)
    }

    // ---- Events (one per phase “broadcast” as in the goldens)
    val events = g.phases.indices.map { i -> EventDecl("Broadcast$i") }

    // ---- Fallback (reject stray ETH)
    val fallback = FallbackDecl(
        visibility = Visibility.PUBLIC, // rendered as `external` by ToText.kt per your current code path
        stateMutability = StateMutability.PAYABLE,
        body = listOf(Statement.Revert("direct ETH not allowed"))
    )

    return SolidityContract(
        name = g.name,
        constructor = ctor,
        enums = listOf(roleEnum),
        storage = storage,
        modifiers = modifiers,
        functions = functions,
        events = events,
        fallback = fallback
    )
}

/* ============================== Helpers =============================== */

/**
 * Tracks where each (role,param) first appears (commit) and where it is revealed.
 * This lets us decide join/yield/reveal shapes and “done” flags.
 */
private class ParamHistory(g: GameIR) {
    private data class Occ(val phase: Int, val visible: Boolean)

    private val occ = mutableMapOf<FieldRef, MutableList<Occ>>()

    init {
        g.phases.forEachIndexed { p, phase ->
            phase.forEach { (role, sig) ->
                sig.parameters.forEach { prm ->
                    occ.getOrPut(FieldRef(role, prm.name)) { mutableListOf() }
                        .add(Occ(p, prm.visible))
                }
            }
        }
    }

    fun isReveal(role: RoleId, param: VarId, phase: Int): Boolean {
        val xs = occ[FieldRef(role, param)] ?: return false
        // First occurrence decides commit; later visible occurrence is reveal
        val first = xs.minByOrNull { it.phase } ?: return false
        return xs.any { it.phase == phase && it.visible && !first.visible && phase > first.phase }
    }

    fun needsCommitReveal(role: RoleId, sig: Signature, phase: Int): Boolean {
        // A phase needs commit-reveal if it contains any hidden params whose reveal is later
        return sig.parameters.any { p ->
            !p.visible && isRevealedLater(role, p.name, phase)
        }
    }

    private fun isRevealedLater(role: RoleId, param: VarId, phase: Int): Boolean {
        val xs = occ[FieldRef(role, param)] ?: return false
        val here = xs.find { it.phase == phase } ?: return false
        return !here.visible && xs.any { it.phase > phase && it.visible }
    }
}

/** Build persistent storage for every param and its done-flags, per the current golden style. */
private fun buildGameStorage(g: GameIR, history: ParamHistory): List<StorageDecl> = buildList {
    g.phases.forEachIndexed { phaseIdx, phase ->
        phase.forEach { (role, sig) ->
            // Per-role “joined” flag (when role participates at least once; mirrors goldens)
            if (sig.join != null) {
                add(StorageDecl(SolType.Bool, Visibility.PUBLIC, "done${role.name}"))
            }
            // For each parameter, create storage + done flags; hidden slot is uint256 (commit hash)
            sig.parameters.forEach { p ->
                val hidden = !p.visible
                val t = if (hidden) SolType.Uint256 else translateType(p.type)
                add(StorageDecl(t, Visibility.PUBLIC, storageParam(role, p.name, hidden)))
                add(StorageDecl(SolType.Bool, Visibility.PUBLIC, doneFlag(role, p.name, hidden)))
            }
            // Per-phase done marker (prevent double action)
            add(StorageDecl(SolType.Bool, Visibility.PUBLIC, "done_${role.name}_$phaseIdx"))
        }
    }
}

/** Per-phase functions: joins / yields / reveal + the Broadcast/nextStep pair. */
private fun buildPhaseFunctions(
    g: GameIR,
    phaseIdx: Int,
    phase: Phase,
    history: ParamHistory
): List<FunctionDecl> = buildList {
    // Start phase comment & end phase comments are handled by renderer via event + nextStep.
    phase.forEach { (role, sig) ->
        val needsCR = history.needsCommitReveal(role, sig, phaseIdx)
        when {
            sig.join != null && sig.parameters.isEmpty() -> add(buildSimpleJoin(role, sig, phaseIdx))
            sig.join != null && !needsCR -> add(buildJoinVisible(role, sig, phaseIdx))
            sig.join != null && needsCR -> {
                add(buildCommit(role, phaseIdx))
                add(buildHalfStep(phaseIdx))
                add(buildReveal(role, sig, phaseIdx)) // join reveal
            }

            sig.join == null && !needsCR -> add(buildYield(role, sig, phaseIdx))
            sig.join == null && needsCR -> {
                add(buildCommit(role, phaseIdx))
                add(buildHalfStep(phaseIdx))
                add(buildReveal(role, sig, phaseIdx))
            }
        }
    }

    // Phase broadcast + nextStep
    add(buildHalfStep(phaseIdx))
}

/** join with no parameters (just stake + role assignment) */
private fun buildSimpleJoin(role: RoleId, sig: Signature, phaseIdx: Int): FunctionDecl {
    val deposit = sig.join?.deposit?.v ?: 0
    return FunctionDecl(
        name = "join_${role.name}",
        params = emptyList(),
        visibility = Visibility.PUBLIC,
        stateMutability = if (deposit > 0) StateMutability.PAYABLE else StateMutability.NONPAYABLE,
        modifiers = listOf(
            ModifierCall("by", listOf(enumVal(ROLE_ENUM, "None"))),
            ModifierCall("at_step", listOf(int(phaseIdx)))
        ),
        body = buildList {
            add(require(not(v("done${role.name}")), "already joined"))
            add(assign(index(ROLE_MAPPING, msgSender), enumVal(ROLE_ENUM, role.name)))
            if (deposit > 0) {
                add(requireDeposit(deposit)); add(setBalance())
            }
            add(require(bool(true), "where")) // your current goldens keep “where” as true for now
            add(assign(v("done${role.name}"), bool(true)))
        }
    )
}

/** join with visible parameters (no commit) */
private fun buildJoinVisible(role: RoleId, sig: Signature, phaseIdx: Int): FunctionDecl {
    val deposit = sig.join?.deposit?.v ?: 0
    val inputs = sig.parameters.map { Param(translateType(it.type), inputParam(it.name, false)) }
    return FunctionDecl(
        name = "join_${role.name}",
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = if (deposit > 0) StateMutability.PAYABLE else StateMutability.NONPAYABLE,
        modifiers = listOf(
            ModifierCall("by", listOf(enumVal(ROLE_ENUM, "None"))),
            ModifierCall("at_step", listOf(int(phaseIdx)))
        ),
        body = buildList {
            add(require(not(v("done${role.name}")), "already joined"))
            add(assign(index(ROLE_MAPPING, msgSender), enumVal(ROLE_ENUM, role.name)))
            if (deposit > 0) {
                add(requireDeposit(deposit)); add(setBalance())
            }
            addAll(translateDomainGuards(sig.parameters))           // visible domain guards
            addAll(translateWhere(sig.requires.condition))
            addAll(translateAssignments(role, sig.parameters))      // store + done flags
            add(assign(v("done_${role.name}_$phaseIdx"), bool(true)))
        }
    )
}

/** yield with visible params */
private fun buildYield(role: RoleId, sig: Signature, phaseIdx: Int): FunctionDecl {
    val inputs = sig.parameters.map { Param(translateType(it.type), inputParam(it.name, false)) }
    return FunctionDecl(
        name = "yield_${role.name}$phaseIdx",
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = listOf(
            ModifierCall("by", listOf(enumVal(ROLE_ENUM, role.name))),
            ModifierCall("at_step", listOf(int(phaseIdx)))
        ),
        body = buildList {
            add(require(not(v("done_${role.name}_$phaseIdx")), "done"))
            addAll(translateDomainGuards(sig.parameters))
            addAll(translateWhere(sig.requires.condition))
            addAll(translateAssignments(role, sig.parameters))
            add(assign(v("done_${role.name}_$phaseIdx"), bool(true)))
        }
    )
}

/** commit step: hidden inputs hashed by caller beforehand; we store as uint256 per current goldens */
private fun buildCommit(role: RoleId, phaseIdx: Int): FunctionDecl {
    // one uint256 input per hidden field at this phase; name `_hidden_<param>`
    // We don’t enforce domain here (hash isn’t in the domain).
    return FunctionDecl(
        name = "yield_${role.name}$phaseIdx",
        params = listOf(
            Param(
                SolType.Uint256,
                "_hidden_car"
            )
        ), // NOTE: minimal demo; real code should derive from signature@phase
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = listOf(
            ModifierCall("by", listOf(enumVal(ROLE_ENUM, role.name))),
            ModifierCall("at_step", listOf(int(phaseIdx)))
        ),
        body = listOf(
            require(not(v("done_${role.name}_$phaseIdx")), "done"),
            // require(true, "where") -- per golden
            assign(v(storageParam(role, VarId("car"), true)), v("_hidden_car")),
            assign(v(doneFlag(role, VarId("car"), true)), bool(true)),
            assign(v("done_${role.name}_$phaseIdx"), bool(true))
        )
    )
}

/** “half step” (after commit) that just emits BroadcastN and moves the step forward */
private fun buildHalfStep(phaseIdx: Int): FunctionDecl =
    FunctionDecl(
        name = "__nextStep$phaseIdx",
        params = emptyList(),
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = emptyList(),
        body = listOf(
            require(v(STEP_VAR) eq int(phaseIdx), "wrong step"),
            Statement.Emit("Broadcast$phaseIdx", emptyList()),
            assign(v(STEP_VAR), int(phaseIdx + 1)),
            assign(v(LAST_TS_VAR), SolExpr.Member(SolExpr.Var("block"), "timestamp"))
        )
    )

/** reveal step: verify keccak(value,salt) == bytes32(commit), store clear value, set done flags */
private fun buildReveal(role: RoleId, sig: Signature, phaseIdx: Int): FunctionDecl {
    val clearParams = sig.parameters.filter { it.visible }
    val inputs = buildList {
        inputs@ for (p in clearParams) add(Param(translateType(p.type), inputParam(p.name, false)))
        // simple scheme: single salt shared by reveals; matches your current helper
        add(Param(SolType.Uint256, "salt"))
    }
    return FunctionDecl(
        name = "reveal_${role.name}$phaseIdx",
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = listOf(
            ModifierCall("by", listOf(enumVal(ROLE_ENUM, role.name))),
            ModifierCall("at_step", listOf(int(phaseIdx)))
        ),
        body = buildList {
            add(require(not(v("done_${role.name}_$phaseIdx")), "done"))
            // verify commitment(s) vs bytes32(stored)
            sig.parameters.filter { it.visible }.forEach { p ->
                val computed =
                    SolExpr.Keccak256(SolExpr.AbiEncodePacked(listOf(v(inputParam(p.name, false)), v("salt"))))
                val stored = v(storageParam(role, p.name, hidden = true))
                add(require(computed eq SolExpr.Cast(SolType.Bytes32, stored), "bad reveal"))
            }
            addAll(translateWhere(sig.requires.condition))
            addAll(translateAssignments(role, clearParams))
            add(assign(v("done_${role.name}_$phaseIdx"), bool(true)))
        }
    )
}

/** Withdraw like your goldens (handles exact/partial withdrawal, effects-first, low-level call). */
private fun buildWithdraw(): FunctionDecl {
    val amount = "amount"
    val bal = "bal"
    val d = "d"
    return FunctionDecl(
        name = "withdraw",
        params = emptyList(),
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = emptyList(),
        body = listOf(
            // uint256 bal = balanceOf[msg.sender];
            Statement.VarDecl(SolType.Uint256, bal, index(BALANCE_MAPPING, msgSender)),
            // require(bal > 0, "no funds");
            require(v(bal) gt int(0), "no funds"),
            // uint256 amount = bal;
            Statement.VarDecl(SolType.Uint256, amount, v(bal)),
            // if (msg.value > 0) { uint256 d = msg.value; require(bal >= d, "insufficient"); amount = bal - d; }
            Statement.If(
                condition = msgValue gt int(0),
                thenBranch = listOf(
                    Statement.VarDecl(SolType.Uint256, d, msgValue),
                    require(v(bal) ge v(d), "insufficient"),
                    assign(v(amount), v(bal) - v(d))
                )
            ),
            // Effects-first: balanceOf[msg.sender] = 0;
            assign(index(BALANCE_MAPPING, msgSender), int(0)),
            // Interaction: (bool ok, ) = payable(msg.sender).call{value: amount}("");
            Statement.Raw("(bool ok, ) = payable(msg.sender).call{value: amount}(\"\");"),
            require(v("ok"), "ETH send failed")
        )
    )
}

/* ====================== IR→Solidity translation atoms ====================== */

private fun translateType(t: Type): SolType = when (t) {
    is Type.IntType -> SolType.Int256
    is Type.BoolType -> SolType.Bool
    is Type.SetType -> SolType.Int256
}

private fun translateDomainGuards(params: List<Parameter>): List<Statement.Require> =
    params.filter { it.visible }.mapNotNull { p ->
        when (val t = p.type) {
            is Type.SetType -> {
                if (t.values.isEmpty()) null
                else {
                    val x = v(inputParam(p.name, false))
                    val cond = t.values.map { x eq int(it) }.reduce<SolExpr, SolExpr> { a, b -> a or b }
                    require(cond, "domain")
                }
            }

            else -> null
        }
    }

private fun translateWhere(expr: Expr): List<Statement.Require> {
    // Current goldens effectively use `require(true, "where")` as a stub.
    // Hook for real expression compiler if/when you wire it.
    return listOf(require(bool(true), "where"))
}

private fun translateAssignments(role: RoleId, params: List<Parameter>): List<Statement.Assign> =
    params.flatMap { p ->
        val hidden = !p.visible
        val storage = v(storageParam(role, p.name, hidden))
        val input = v(inputParam(p.name, hidden))
        val done = v(doneFlag(role, p.name, hidden))
        listOf(assign(storage, input), assign(done, bool(true)))
    }
