package vegas.frontend

import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import vegas.generated.VegasLexer
import vegas.generated.VegasParser
import java.net.URI
import java.nio.file.Paths


fun parseCode(code: String, uri: URI = URI.create("inmemory:repl.vg")): ProgramAst {
    // Ensure there's always a withdraw statement
    val fullCode = if (!code.contains("withdraw")) "$code; withdraw {}" else code

    // Give ANTLR a source name that matches the URI (helps error messages)
    val chars = CharStreams.fromString(fullCode, uri.toString())
    val tokens = CommonTokenStream(VegasLexer(chars))
    val ast = VegasParser(tokens).program()

    return AstTranslator(uri).visitProgram(ast)
}

fun parseFile(inputFilename: String): ProgramAst {
    val path = Paths.get(inputFilename)
    val chars = CharStreams.fromPath(path) // source name = path.toString()
    val tokens = CommonTokenStream(VegasLexer(chars))
    val ast = VegasParser(tokens).program()

    return AstTranslator(path.toUri()).visitProgram(ast)
}
