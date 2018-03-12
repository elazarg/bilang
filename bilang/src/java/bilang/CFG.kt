package bilang

data class Node(val stmt: Stmt?, val nextList: List<Node>)

// Probably completely wrong

object CFG {
    fun toCfg(prog: Program): Node = toCfg(prog.block.stmts)
    fun toCfg(stmts: List<Stmt>, _next: Node = Node(null, listOf())): Node {
        var next = _next
        for (last in stmts.reversed()) {
            next = when (last) {
                is Stmt.Block -> toCfg(last.stmts, next)
                is Stmt.If -> Node(last, listOf(
                        toCfg(last.ifTrue.stmts, next),
                        toCfg(last.ifFalse.stmts, next)
                ))
                is Stmt.ForYield -> Node(last,
                        listOf(toCfg(last.block.stmts, next))
                )
                else -> Node(last, listOf(next))
            }
        }
        return next
    }
}
