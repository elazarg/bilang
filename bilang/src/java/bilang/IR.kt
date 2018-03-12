package bilang

import kotlin.coroutines.experimental.buildSequence

sealed class IR {

    interface Exp
    data class Var(val n: Int): Exp
    data class Const(val k: bilang.Exp.Const): Exp

    data class Assign(val target: Var, val left: Exp, val op: String, val right: Exp): IR()
    data class UnOp(val target: Var, val op: String, val exp: Exp): IR()
    data class Mov(val target: Var, val exo: Exp): IR()
    data class Yield(val sender: Var, val targets: List<Var>): IR()
    data class Jump(val target: Int, val cond: Exp): IR()
    data class Require(val cond: Exp): IR()
    data class Assume(val cond: Var): IR()
    data class Assert(val cond: Exp): IR()
    data class Label(val n: Int): IR()
}

object Fresh {
    private var v = 0
    fun vvar(): IR.Var {
        v += 1
        return IR.Var(v)
    }

    private var n = 0
    fun label(): IR.Label {
        n += 1
        return IR.Label(n)
    }


}

fun varOf(v: Exp.Var) = IR.Var(v.name.hashCode())


fun stmtToIR(stmt: Stmt): Sequence<IR> {
    return when (stmt) {
        is Stmt.Def.VarDef -> expToIR(stmt.init, varOf(stmt.dec.name))
        is Stmt.Def.YieldDef -> {
            // for each packet
            // require actual packet match formal packet for the appropriate sender
            val sender = Fresh.vvar()
            val packet = stmt.packets[0]
            val v = Fresh.vvar()
            buildSequence {
                yield   (IR.Yield(sender, packet.params.map {varOf(it.name)} ))
                yieldAll(expToIR(packet.where, v))
                yield   (IR.Require(v))
            }
            TODO()
        }
        is Stmt.Def.JoinDef ->
            TODO("Same as yield, but assign the sender instead of checking")
        is Stmt.Def.JoinManyDef -> TODO()
        is Stmt.Block -> buildSequence {
            for (s in stmt.stmts)
                yieldAll(stmtToIR(s))
        }
        is Stmt.Assign -> expToIR(stmt.exp, varOf(stmt.target))
        is Stmt.Reveal -> {
            val targets = listOf(varOf(stmt.target))
            val sender = TODO()
            sequenceOf(IR.Yield(sender, targets))
        }
        is Stmt.If -> {
            val trueLabel = Fresh.label()
            val endLabel = Fresh.label()
            val vc = Fresh.vvar()
            buildSequence {
                yieldAll(expToIR(stmt.cond, vc))
                yield   (IR.Jump(trueLabel.n, vc))
                yieldAll(stmtToIR(stmt.ifFalse))
                yield   (IR.Jump(endLabel.n, vc))
                yield   (trueLabel)
                yieldAll(stmtToIR(stmt.ifTrue))
                yield   (endLabel)
            }
        }
        is Stmt.ForYield -> {
            val startLabel = Fresh.label()
            val endLabel = Fresh.label()
            buildSequence {
                yield(startLabel)
                yieldAll(acceptPacket(stmt.packet))
                yieldAll(stmtToIR(stmt.block))
                yield(IR.Jump(startLabel.n, varOf(Exp.Var("true"))))
                yield(endLabel)
            }
        }

        is Stmt.Transfer -> TODO()
    }
}

fun expToIR(exp: Exp, v: IR.Var): Sequence<IR> {
    return when (exp) {
        is Exp.Call -> TODO()
        is Exp.UnOp -> {
            val v1 = Fresh.vvar()
            buildSequence {
                yieldAll(expToIR(exp.operand, v1))
                yield(IR.UnOp(v, exp.op, v1))
            }
        }
        is Exp.BinOp -> {
            val v1 = Fresh.vvar()
            val v2 = Fresh.vvar()
            buildSequence {
                yieldAll(expToIR(exp.left, v1))
                yieldAll(expToIR(exp.right, v2))
                yield(IR.Assign(v, v1, exp.op, v2))
            }
        }
        is Exp.Const -> sequenceOf(IR.Mov(v, IR.Const(exp)))
        is Exp.Var -> sequenceOf(IR.Mov(v, varOf(exp)))
        is Exp.Member -> TODO()
        is Exp.Cond -> {
            fun block(e: Exp) = Stmt.Block(listOf(Stmt.Assign(Exp.Var(v.n.toString()), e)))
            stmtToIR(Stmt.If(exp.cond, block(exp.ifTrue), block(exp.ifFalse)))
        }
        else -> throw AssertionError()
    }
}

fun acceptPacket(p: Packet): Sequence<IR> { TODO() }
