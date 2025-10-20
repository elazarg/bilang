# Vegas Language Support (VS Code)

Language server and VS Code extension for the **Vegas** game-synthesis language.
Provides diagnostics, (basic) hover, and **semantic syntax highlighting**.

## Features

* **Live diagnostics** (parse/type errors) on open/change via LSP `publishDiagnostics`.
* **Hover (placeholder)** returns a simple message for now.
* **Semantic tokens** (keywords, variables, numbers, operators, etc.) — the server advertises a semantic-token legend and serves full-document tokens.

    * Current token types registered: `keyword`, `variable`, `number`, `operator`, `type`, `string`.
    * The visitor class encodes tokens (5-tuples per LSP: `deltaLine, deltaStart, length, tokenTypeIndex, modifiers`).

## How it works (high level)

* **Server**: Kotlin (LSP4J). Exposes `TextDocumentService` and `WorkspaceService`; registers text sync, hover, and semantic-token capabilities. Entry point runs on stdio.
* **Tokens**: `SemanticTokenVisitor` walks the parse tree and tags identifiers, ints, operators, and grammar-defined keywords.
* **Client (VS Code)**: Activates on `vegas` files and requests diagnostics/hover/tokens like any LSP client (standard VS Code languageclient wiring).

## Requirements

* **Java 17+** (to launch the server). Server runs over **stdio** via `LSPLauncher`.
* **VS Code** recent build (the extension targets current VS Code language features).
* Node.js (for building the VS Code client).

## Install / Build (dev workflow)

1. **Build the language server jar** (Maven/Gradle as in your repo). Ensure the fat/shaded jar is available to the extension (e.g., `vegas/server/vegas-…-jar-with-dependencies.jar`).
2. **Install client deps**:

   ```bash
   cd vegas
   npm ci
   npm run compile
   ```
3. **Run the Extension Host**:

    * In VS Code, open the **vegas** folder and press **F5** (“Run Extension”).
    * In the Extension Development Host window, open a `.vg` file. The server starts and diagnostics/tokens flow.

> Packaging: the server’s `main` uses stdio and must be launched by the client; the LSP entrypoint is in Kotlin (see `main()` in `Server.kt`).

## Project layout (relevant pieces)

* `vegas/src/*` — VS Code extension (TypeScript).
* `src/main/kotlin/vegas/lsp/*` — LSP server:

    * `Server.kt` – capabilities, semantic-token legend, stdio launcher.
    * `VegasTextDocumentService.kt` – document open/change → validate & publish diagnostics; hover; semanticTokens/full.
    * `SemanticTokenVisitor.kt` – parse-tree walk → encoded tokens.
    * `VegasWorkspaceService.kt` – stubbed workspace notifications.

## Semantic tokens details

* **Legend** (server-side): `keyword`, `variable`, `number`, `operator`, `type`, `string`. Indices correspond to their positions in the array.
* **Visitor mapping** (examples):
  `ID → variable`, `INT → number`, grammar ranges map to `keyword` or `operator`. Encoded with running `deltaLine/deltaChar`.

## Troubleshooting

* **No colors after “adding spans”**: If semantic tokens are registered but the handler throws or returns mismatched data, VS Code prefers semantics and your TextMate colors disappear. Ensure the server advertises only what it serves (legend ↔ visitor indices) and returns `IntArray`/list in multiples of 5. See `Server.kt` (legend) and `VegasTextDocumentService.semanticTokensFull`.
* **Diagnostics don’t show**: Confirm `didOpen`/`didChange` store the text and `validateDocument` runs; errors are published via `publishDiagnostics`.
* **Server doesn’t start**: You need Java on PATH; the server’s `main()` uses stdio.

## Roadmap

* Proper hover content (types/symbol docs).
* Incremental sync & range semantic tokens (optional).
* Code actions, completions.
