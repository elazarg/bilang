package vegas.lsp

import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.services.TextDocumentService
import vegas.frontend.GameAst
import vegas.StaticError
import vegas.typeCheck
import org.eclipse.lsp4j.SemanticTokens
import org.eclipse.lsp4j.SemanticTokensParams
import vegas.generated.VegasLexer
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import vegas.frontend.Span
import vegas.frontend.parseCode
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

    private fun spanToRange(span: Span?): Range {
        return if (span == null) {
            Range(Position(0, 0), Position(0, Int.MAX_VALUE))
        } else {
            Range(Position(span.startLine-1, span.startCol-1), Position(span.endLine-1,span.endCol))
        }
    }

    private fun validateDocument(uri: String) {
        val content = documentManager[uri] ?: return
        val diagnostics = mutableListOf<Diagnostic>()
        try {
            val program: GameAst = parseCode(content)
            typeCheck(program)
        } catch (e: StaticError) {
            diagnostics.add(Diagnostic(spanToRange(e.span()), e.message, DiagnosticSeverity.Error, "vegas"))
        } catch (e: Exception) {
            val range = Range(Position(0, 0), Position(0, Int.MAX_VALUE))
            diagnostics.add(Diagnostic(range, "Parsing error: " + e.message, DiagnosticSeverity.Error, "vegas"))
            diagnostics.add(Diagnostic(range, "Parsing error: " + e.stackTraceToString(), DiagnosticSeverity.Error, "vegas"))
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
        tokens.fill()

        val encoded = encodeToken(tokens.tokens, server.tokenTypes)
        return CompletableFuture.completedFuture(SemanticTokens(encoded))
    }
}
