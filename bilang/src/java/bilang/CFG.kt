package bilang
import org.graphstream.graph.*
import org.graphstream.graph.implementations.SingleGraph



class Node(val id: Int, val stmt: Stmt?, var prevList: List<Node>)

object CFG {
    var lastId = 0
    fun toCfg(prog: Program): Node {
        lastId += 1
        val root = Node(lastId, null, listOf())
        toCfg(prog.block.stmts, listOf(root))
        return root
    }

    fun toCfg(stmts: List<Stmt>, _prev: List<Node>): List<Node> {
        var prev = _prev
        for (last in stmts) {
            lastId += 1
            when (last) {
                is Stmt.Block -> prev = toCfg(last.stmts, prev)
                is Stmt.If -> prev = listOf(Node(lastId, last,
                        toCfg(last.ifTrue.stmts, prev) + toCfg(last.ifFalse.stmts, prev)
                ))
                is Stmt.ForYield -> prev += listOf(Node(lastId, last, toCfg(last.block.stmts, prev)))
                else -> prev = listOf(Node(lastId, last, prev))
            }
        }
        return prev
    }

    fun cfgToGraph(cfg: Node) {
        val graph = SingleGraph("CFG")
        val nodes = mutableSetOf(cfg)
        while (nodes.isNotEmpty()) {
            val n = nodes.first()
            nodes.remove(n)
            val prevs = n.prevList
            val index1 = graph.addNode<org.graphstream.graph.Node>(n.id.toString()).index
            for (p in prevs) {
                val index2 = graph.addNode<org.graphstream.graph.Node>(p.id.toString()).index
                graph.addEdge<org.graphstream.graph.Edge>("$index1 $index2", index1, index2)
            }

        }
        graph.display()
    }
}

fun main(args: Array<String>) {
    val program = parse("examples/ThreeWayLottery.bi")
    CFG.cfgToGraph(CFG.toCfg(program))
}