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
    return "done_${storageParam(role, param, hidden)}"
}

fun phaseDone(role: RoleId, phase: Int): String {
    return "done_Phase${phase}_${role.name}"
}

fun roleDone(role: RoleId): String {
    return "done_${role.name}"
}

fun roleAddr(role: RoleId): String = "address_${role.name}"

// ===== Functions =====

fun joinFunc(role: RoleId): String = "join_${role.name}"
fun yieldFunc(role: RoleId, phase: Int): String = "yield_Phase${phase}_${role.name}"
fun revealFunc(role: RoleId, phase: Int): String = "reveal_Phase${phase}_${role.name}"
fun nextPhaseFunc(phase: Int): String = "__nextPhase_Phase$phase"

// ===== Events =====

fun broadcastEvent(phase: Int): String = "Broadcast_Phase$phase"

// ===== Parameters =====

fun inputParam(param: VarId, hidden: Boolean): String {
    val prefix = if (hidden) "hidden_" else ""
    return "_$prefix${param.name}"
}

// ===== Built-in Names =====

const val ROLE_ENUM = "Role"
const val ROLE_MAPPING = "role"
const val BALANCE_MAPPING = "balanceOf"
const val PHASE_VAR = "phase"
const val LAST_TS_VAR = "lastTs"
const val PHASE_TIME_CONST = "PHASE_TIME"
