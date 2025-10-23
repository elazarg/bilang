package vegas.backend.solidity

import vegas.RoleId
import vegas.VarId


/**
 * Centralized naming scheme for all Solidity identifiers.
 * Single source of truth for variable/function name generation.
 */
    // ===== Storage Variables =====

    fun storageParam(role: RoleId, param: VarId, hidden: Boolean): String {
        val prefix = if (hidden) "hidden_" else ""
        return "${role.name}_$prefix${param.name}"
    }

    fun doneFlag(role: RoleId, param: VarId, hidden: Boolean): String {
        return storageParam(role, param, hidden) + "_done"
    }

    fun stepDone(role: RoleId, step: Int): String {
        return "done_${role.name}_$step"
    }

    fun roleDone(role: RoleId): String {
        return "done${role.name}"
    }

    // ===== Commit-Reveal Infrastructure =====

    fun commitMap(role: RoleId): String = "commits${role.name}"
    fun timeMap(role: RoleId): String = "times${role.name}"
    fun halfStepFlag(role: RoleId): String = "halfStep${role.name}"

    // ===== Functions =====

    fun joinFunc(role: RoleId): String = "join_${role.name}"
    fun joinCommitFunc(role: RoleId): String = "join_commit_${role.name}"
    fun halfStepFunc(role: RoleId): String = "__nextHalfStep${role.name}"
    fun yieldFunc(role: RoleId, step: Int): String = "yield_${role.name}$step"
    fun revealFunc(role: RoleId, step: Int): String = "reveal_${role.name}$step"
    fun withdrawFunc(role: RoleId, step: Int): String = "withdraw_${step}_${role.name}"
    fun nextStepFunc(step: Int): String = "__nextStep$step"

    // ===== Events =====

    fun broadcastEvent(step: Int): String = "Broadcast$step"
    fun broadcastHalfEvent(role: RoleId): String = "BroadcastHalf${role.name}"

    // ===== Parameters =====

    fun inputParam(param: VarId, hidden: Boolean): String {
        val prefix = if (hidden) "hidden_" else ""
        return "_$prefix${param.name}"
    }

    // ===== Built-in Names =====

    const val ROLE_ENUM = "Role"
    const val ROLE_MAPPING = "role"
    const val BALANCE_MAPPING = "balanceOf"
    const val STEP_VAR = "step"
    const val LAST_TS_VAR = "lastTs"
    const val STEP_TIME_CONST = "STEP_TIME"
