package vegas.ir

import vegas.Rational
import vegas.frontend.Role

// ===== Core =====

data class ProgramIR(
    val name: String,
    val roles: Set<Role>,
    val blocks: List<Block>,            // total order: blocks[0], blocks[1], ...
    val payoffs: Map<Role, Expr>
) {
    init { require(wellFormed()) { "Protocol fails well-formedness checks" } }
    private fun wellFormed(): Boolean = WfChecks(this).runAll()
}

/**
 * A Block is a simultaneous-move step.
 * - All moves in the same block see the SAME pre-state snapshot.
 * - At most one move per role in a block.
 * - Evaluation order inside a block does not matter (commutes).
 */
data class Block(
    val id: BlockId,
    val moves: List<Move>
)

// Unique ids (simple strings are fine; keep types nominal for safety).
@JvmInline value class BlockId(val s: String)
@JvmInline value class MoveId(val s: String)

// ===== Moves & Parameters =====

data class Move(
    val id: MoveId,
    val by: Role,             // a participant or Role.Chance
    val kind: MoveKind,       // JOIN, SUBMIT, REVEAL, CHANCE
    val params: List<Param>,  // input values this move provides (commit, submit, reveal)
    val guard: Expr = Expr.Bool(true) // enabled iff guard(pre-state) == true
)

enum class MoveKind { JOIN, SUBMIT, REVEAL, CHANCE }

/**
 * A parameter is just a name and a type.
 * Visibility is *inferred* from the type and the block index:
 *  - PUBLIC      : any non-Hidden type, once provided, is visible to all from next block onward
 *  - HIDDEN(T)   : commitment at commit block; value is known only to the owner until explicitly REVEALed
 *  - OPT(T)      : adds an undefined alternative; IsDef/IsUndef predicates expose definedness
 */
data class Param(
    val name: String,
    val type: Type
)

// ===== Types (commit–reveal is a type) =====

sealed class Type {
    object IntType : Type()
    object BoolType : Type()
    data class Range(val lo: Int, val hi: Int) : Type()
    data class Subset(val values: Set<Int>) : Type()
    data class Enum(val name: String, val values: List<String>) : Type()
    data class Hidden(val inner: Type) : Type()     // declared commitment
    data class Opt(val inner: Type) : Type()
}

// ===== Expressions (guards & payoffs) =====

sealed class Expr {
    // literals
    data class IntLit(val v: Int) : Expr()
    data class Bool(val v: Boolean) : Expr()

    // field reference: value of move.param produced in a *prior* block
    data class Field(val move: MoveId, val param: String) : Expr()

    // definedness (needed for Opt and commit-reveal flows)
    data class IsDef(val of: Field) : Expr()
    data class IsUndef(val of: Field) : Expr()

    // arithmetic
    data class Add(val l: Expr, val r: Expr) : Expr()
    data class Sub(val l: Expr, val r: Expr) : Expr()
    data class Mul(val l: Expr, val r: Expr) : Expr()
    data class Div(val l: Expr, val r: Expr) : Expr() // trunc toward zero

    // comparisons & logic
    data class Eq(val l: Expr, val r: Expr) : Expr()
    data class Ne(val l: Expr, val r: Expr) : Expr()
    data class Lt(val l: Expr, val r: Expr) : Expr()
    data class Le(val l: Expr, val r: Expr) : Expr()
    data class Gt(val l: Expr, val r: Expr) : Expr()
    data class Ge(val l: Expr, val r: Expr) : Expr()
    data class And(val l: Expr, val r: Expr) : Expr()
    data class Or(val l: Expr, val r: Expr) : Expr()
    data class Not(val x: Expr) : Expr()

    // ternary
    data class Ite(val c: Expr, val t: Expr, val e: Expr) : Expr()
}

// ===== Chance support (optional weights) =====

/**
 * If by == Role.Chance and the move has a single parameter of a finite type,
 * the backend may treat it as a chance node. Optional weights allow non-uniform chance.
 */
data class ChanceWeights(
    val move: MoveId,
    val weights: Map<ConstValue, Rational> // sum==1; ConstValue comes from the param's finite domain
)

// simple value holder for weights; align with Type domains at lowering time
sealed class ConstValue {
    data class IntV(val v: Int) : ConstValue()
    data class BoolV(val v: Boolean) : ConstValue()
    data class EnumV(val tag: String) : ConstValue()
}

// ===== Well-formedness (sketch) =====

class WfChecks(private val p: ProgramIR) {
    fun runAll(): Boolean =
        blocksAreLinear() &&
                atMostOneMovePerRolePerBlock() &&
                fieldsOnlyFromPriorBlocks() &&
                hiddenPayoffMustReveal() &&
                guardsChainVisible() &&
                arithmeticModelOk()

    private fun blocksAreLinear() = true // by construction: List<Block> is a total order

    private fun atMostOneMovePerRolePerBlock(): Boolean =
        p.blocks.all { b -> b.moves.map { it.by }.distinct().size == b.moves.size }

    /** Guards may reference only values visible on-chain at the start of the block:
     *   - any non-Hidden param from *prior* blocks
     *   - any Hidden param that has been REVEALed in a prior block
     *   - IsDef/IsUndef are allowed if their done-bit is on-chain (always true here)
     * Off-chain analysis may relax this; keep the on-chain rule as default.
     */
    private fun guardsChainVisible(): Boolean = true // implement by walking Expr and checking visibility lattice

    /** Any Expr.Field used in payoffs must be PUBLIC at terminal:
     *   - non-Hidden from some block (always public after its block)
     *   - or Hidden that has a corresponding REVEAL move in a prior block
     */
    private fun hiddenPayoffMustReveal(): Boolean = true // implement: ensure a REVEAL exists before final block

    /** Expressions may only reference prior blocks (no forward refs). */
    private fun fieldsOnlyFromPriorBlocks(): Boolean = true // walk Exprs

    /** Optional: static overflow/zero-div checks under target numeric model. */
    private fun arithmeticModelOk(): Boolean = true
}
