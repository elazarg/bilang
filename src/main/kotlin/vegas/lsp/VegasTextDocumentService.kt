package vegas.lsp

import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.services.TextDocumentService
import vegas.ExpProgram
import vegas.StaticError
import vegas.parseCode
import vegas.typeCheck
import org.eclipse.lsp4j.SemanticTokens
import org.eclipse.lsp4j.SemanticTokensParams
import vegas.generated.VegasLexer
import vegas.generated.VegasParser
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.util.concurrent.CompletableFuture

class VegasTextDocumentService(private val server: VegasLanguageServer) : TextDocumentService {

    private val documentManager = mutableMapOf<String, String>()

    override fun didOpen(params: DidOpenTextDocumentParams) {
        val uri = params.textDocument.uri
        documentManager[uri] = params.textDocument.text
        validateDocument(uri)
    }

    override fun didChange(params: DidChangeTextDocumentParams) {
        val uri = params.textDocument.uri
        documentManager[uri] = params.contentChanges[0].text
        validateDocument(uri)
    }

    override fun didClose(params: DidCloseTextDocumentParams) {
        documentManager.remove(params.textDocument.uri)
    }

    override fun didSave(params: DidSaveTextDocumentParams) {
        // Can be used to trigger validation
    }

    private fun validateDocument(uri: String) {
        val content = documentManager[uri] ?: return
        val diagnostics = mutableListOf<Diagnostic>()
        try {
            val program: ExpProgram = parseCode(content)
            typeCheck(program)
        } catch (e: StaticError) {
            // In a real implementation, you would get line/column info from the parser
            val range = Range(Position(0, 0), Position(0, Int.MAX_VALUE))
            diagnostics.add(Diagnostic(range, e.message, DiagnosticSeverity.Error, "vegas"))
        } catch (e: Exception) {
            val range = Range(Position(0, 0), Position(0, Int.MAX_VALUE))
            diagnostics.add(Diagnostic(range, "Parsing error: " + e.message, DiagnosticSeverity.Error, "vegas"))
        }

        server.getClient().publishDiagnostics(PublishDiagnosticsParams(uri, diagnostics))
    }

    override fun hover(params: HoverParams): CompletableFuture<Hover> {
        // For a more complete implementation, you'd use the symbol table
        // to find the symbol at the given position and return its type.
        return CompletableFuture.completedFuture(
            Hover(
                MarkupContent(
                    MarkupKind.PLAINTEXT,
                    "Vegas Language Hover (Not fully implemented)"
                )
            )
        )
    }
    override fun semanticTokensFull(params: SemanticTokensParams): CompletableFuture<SemanticTokens> {
        val uri = params.textDocument.uri
        val content = documentManager[uri] ?: return CompletableFuture.completedFuture(SemanticTokens(emptyList()))

        val chars = CharStreams.fromString(content)
        val lexer = VegasLexer(chars)
        val tokens = CommonTokenStream(lexer)
        val parser = VegasParser(tokens)
        val tree = parser.program()

        val visitor = SemanticTokenVisitor(server.tokenTypes)
        visitor.visit(tree)

        return CompletableFuture.completedFuture(SemanticTokens(visitor.encodedTokens))
    }
}
