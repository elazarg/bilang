package vegas.lsp

import org.eclipse.lsp4j.launch.LSPLauncher
import java.util.concurrent.Executors
import org.eclipse.lsp4j.InitializeParams
import org.eclipse.lsp4j.InitializeResult
import org.eclipse.lsp4j.ServerCapabilities
import org.eclipse.lsp4j.TextDocumentSyncKind
import org.eclipse.lsp4j.services.LanguageClient
import org.eclipse.lsp4j.services.LanguageClientAware
import org.eclipse.lsp4j.services.LanguageServer
import org.eclipse.lsp4j.services.TextDocumentService
import org.eclipse.lsp4j.services.WorkspaceService
import org.eclipse.lsp4j.SemanticTokensLegend
import org.eclipse.lsp4j.SemanticTokensWithRegistrationOptions
import org.eclipse.lsp4j.SemanticTokenTypes

class VegasLanguageServer : LanguageServer, LanguageClientAware {
    private lateinit var client: LanguageClient
    private val textDocumentService = VegasTextDocumentService(this)
    private val workspaceService = VegasWorkspaceService()


    override fun initialize(params: InitializeParams): java.util.concurrent.CompletableFuture<InitializeResult> {
        val capabilities = ServerCapabilities()
        capabilities.setTextDocumentSync(TextDocumentSyncKind.Full)
        capabilities.setHoverProvider(true)

        // Add the semantic highlighting capability
        val legend = SemanticTokensLegend(tokenTypes, tokenModifiers)
        capabilities.semanticTokensProvider = SemanticTokensWithRegistrationOptions(legend, true) // `true` for full document sync

        val result = InitializeResult(capabilities)
        return java.util.concurrent.CompletableFuture.completedFuture(result)
    }

    override fun shutdown(): java.util.concurrent.CompletableFuture<Any> {
        return java.util.concurrent.CompletableFuture.completedFuture(null)
    }

    override fun exit() {
        // No operation
    }

    override fun getTextDocumentService(): TextDocumentService {
        return textDocumentService
    }

    // This is the corrected implementation
    override fun getWorkspaceService(): WorkspaceService {
        return workspaceService
    }

    override fun connect(client: LanguageClient) {
        this.client = client
    }

    fun getClient(): LanguageClient {
        return client
    }
    val tokenTypes = listOf(
        SemanticTokenTypes.Keyword,
        SemanticTokenTypes.Variable,
        SemanticTokenTypes.Number,
        SemanticTokenTypes.Operator,
        SemanticTokenTypes.Type,
        SemanticTokenTypes.String
    )

    val tokenModifiers = listOf<String>()

}

fun main() {
    val server = VegasLanguageServer()
    val executor = Executors.newSingleThreadExecutor()
    val launcher = LSPLauncher.createServerLauncher(server, System.`in`, System.out, executor) { it }
    server.connect(launcher.remoteProxy)
    launcher.startListening()
}
