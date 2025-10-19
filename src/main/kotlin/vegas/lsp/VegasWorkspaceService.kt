package vegas.lsp

import org.eclipse.lsp4j.DidChangeConfigurationParams
import org.eclipse.lsp4j.DidChangeWatchedFilesParams
import org.eclipse.lsp4j.services.WorkspaceService

class VegasWorkspaceService : WorkspaceService {

    override fun didChangeConfiguration(params: DidChangeConfigurationParams) {
        // A notification sent from the client to the server to signal the change of configuration settings.
    }

    override fun didChangeWatchedFiles(params: DidChangeWatchedFilesParams) {
        // The watched files notification is sent from the client to the server when files watched by the client change.
    }
}
