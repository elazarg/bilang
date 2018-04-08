package bilang
/*
import Exp.*

class Block(val id: Int, val preds: List<Block>)
data class Phi(val exp: Exp, val operands: List<Exp>, val block: Block, val users: Set<Exp>)

class SsaMaker {
    private val currentDef: Map<Var, MutableMap<Int, Exp?>> = mutableMapOf()
    private val incompletePhis: Map<Int, MutableMap<Var, Phi>> = mutableMapOf()
    private val sealedBlocks: MutableSet<Int> = mutableSetOf()

    private fun writeVariable(variable: Var, block: Block, value: Exp?) {
        currentDef.getValue(variable)[block.id] = value
    }

    private fun readVariable(variable: Var, block: Block): Exp? {
        return currentDef.getValue(variable).getOrElse(block.id, { readVariableRecursive(variable, block) })
    }

    private fun readVariableRecursive(variable: Var, block: Block): Exp? {
        val v: Exp? = if (!sealedBlocks.contains(block.id)) {
            val v1 = makePhi(block)
            incompletePhis.getValue(block.id)[variable] = v1
            v1
        } else if (block.preds.size == 1) {
            readVariable(variable, block.preds[0])
        } else {
            val v1 = makePhi(block)
            writeVariable(variable, block, v1)
            for (pred in v1.block.preds)
                v1.appendOperand(readVariable(variable, pred))
            tryRemoveTrivialPhi(v1)
        }
        writeVariable(variable, block, v)
        return v
    }

    private fun tryRemoveTrivialPhi(phi: Phi): Exp? {
        var same: Exp? = null
        for (op in phi.operands) {
            if (op == same || op == phi.exp)
                continue
            if (same != null)
                return phi.exp
            same = op
        }
        if (same == null)
            same = UNDEFINED

        val users = phi.users - phi
        phi.replaceBy(same)

        for (use in users)
            if (use is Phi)
                tryRemoveTrivialPhi(use)
        return same
    }

    private fun sealBlock(block: Block) {
        for (variable in incompletePhis.getValue(block.id))
            addPhiOperands(variable, incompletePhis.getValue(block.id)[variable])
        sealedBlocks.add(block.id)
    }

    fun makePhi(b: Block): Phi = TODO()
}

*/