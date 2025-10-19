package vegas.lsp

import org.antlr.v4.runtime.tree.TerminalNode
import vegas.generated.VegasBaseVisitor
import vegas.generated.VegasParser.*

class SemanticTokenVisitor(private val tokenTypes: List<String>) : VegasBaseVisitor<Unit>() {

    val encodedTokens = mutableListOf<Int>()
    private var lastLine = 0
    private var lastChar = 0

    override fun visitTerminal(node: TerminalNode) {
        val tokenType = when (node.symbol.type) {
            ID -> "variable"
            INT -> "number"
            in T__6..T__11, in T__15..T__20, T__41 -> "keyword"
            in T__22..T__28, in T__30..T__37 -> "operator"
            else -> null
        }

        if (tokenType != null) {
            val typeIndex = tokenTypes.indexOf(tokenType)
            if (typeIndex != -1) {
                val line = node.symbol.line - 1
                val char = node.symbol.charPositionInLine

                val deltaLine = line - lastLine
                val deltaChar = if (deltaLine == 0) char - lastChar else char

                encodedTokens.addAll(listOf(deltaLine, deltaChar, node.text.length, typeIndex, 0))

                lastLine = line
                lastChar = char
            }
        }
    }
}
