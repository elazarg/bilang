package vegas.ir

import vegas.RoleId
import vegas.VarId
import vegas.FieldRef

// ---------- types & domains ----------
sealed class Type {
    object IntType : Type()
    object BoolType : Type()
    data class SetType(val values: Set<Int>) : Type()
}

/**
 * A Parameter represents data provided when executing an action.
 *
 * "visible" means reveal if "invisible" was already declared. A second "invisible" might be "reconsidered", or malformed.
 */
data class Parameter(
    val name: VarId,
    val type: Type,
    val visible: Boolean,
)

// Expression are mostly straightforward
sealed class Expr {
    // literals
    data class IntLit(val v: Int) : Expr()
    data class BoolLit(val v: Boolean) : Expr()

    data class Field(val field: FieldRef) : Expr()

    data class IsDefined(val field: FieldRef) : Expr()

    // arithmetic
    data class Add(val l: Expr, val r: Expr) : Expr()
    data class Sub(val l: Expr, val r: Expr) : Expr()
    data class Mul(val l: Expr, val r: Expr) : Expr()
    data class Div(val l: Expr, val r: Expr) : Expr()
    data class Neg(val x: Expr) : Expr()

    // comparisons
    data class Eq(val l: Expr, val r: Expr) : Expr()
    data class Ne(val l: Expr, val r: Expr) : Expr()
    data class Lt(val l: Expr, val r: Expr) : Expr()
    data class Le(val l: Expr, val r: Expr) : Expr()
    data class Gt(val l: Expr, val r: Expr) : Expr()
    data class Ge(val l: Expr, val r: Expr) : Expr()

    // boolean
    data class And(val l: Expr, val r: Expr) : Expr()
    data class Or (val l: Expr, val r: Expr) : Expr()
    data class Not(val x: Expr) : Expr()
    data class Ite(val c: Expr, val t: Expr, val e: Expr) : Expr()
}

/**
 * Requirements specify when an action can execute.
 *
 * after: Control dependencies (must-happen-before). Forms DAG.
 * sees: Data dependencies (which fields this action's condition reads).
 *       WF condition: Fields in condition must appear in sees.
 * condition: Logical guard enabling action.
 *
 * UNDEFINED SEMANTICS:
 * If condition references undefined field (action not yet complete),
 * condition evaluates to false (action not enabled).
 * All backends implement via "done flags": <action>_<param>_done.
 */
data class Requirement(
    val captures: Set<FieldRef>,        // fields this guard MAY read (must be from earlier phases)
    val condition: Expr             // boolean; see "Guard scheduling"
)

/**
 * A Signature is something a role does: join, submit data, commit or reveal hidden info.
 */
data class Signature(
    val join: Boolean,              // true if this is the role's "join" step (binds address, deposits, etc.)
    val parameters: List<Parameter>,
    val requires: Requirement      // guard for this role's action (snapshot semantics)
)

/** Exactly one Signature per RoleId in a Phase.
 *
 * SIMULTANEITY SEMANTICS:
 * Simultaneous (independent) if neither depends on the other
 * (no path in dependency graph). Simultaneous actions:
 * - Compute infosets and legality from SAME pre-state snapshot
 * - Can execute in any order (commute)
 * - Belong to same information set if they can't observe each other's choices
 * */
typealias Phase = Map<RoleId, Signature>

/**
 * A GameIR describes a multi-party interaction where roles perform actions
 * that may depend on each other, leading to payoffs for each role.
 */
data class GameIR(
    val name: String,
    val roles: Set<RoleId>,
    val phases: List<Phase>,        // index is phase order; straight-path
    val payoffs: Map<RoleId, Expr>    // evaluated at terminal
)
