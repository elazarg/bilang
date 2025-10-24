package vegas.frontend

import java.net.URI
import java.util.IdentityHashMap

data class Span(
    val uri: URI,
    val startLine: Int, val startCol: Int,
    val endLine: Int,   val endCol: Int
)

object SourceLoc {
    private val table = IdentityHashMap<Ast, Span>()

    fun copy(to: Ast, from: Ast) { table[to] = table[from] }
    fun set(node: Ast, span: Span) { table[node] = span }
    fun get(node: Ast): Span? = table[node]
}
