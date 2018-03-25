package bilang

import java.nio.file.Paths

import org.antlr.v4.runtime.*

import bilang.generated.*

fun parse(inputFilename: String) =
        BiLangParser(CommonTokenStream(BiLangLexer(CharStreams.fromPath(Paths.get(inputFilename))))).program()

fun main(args: Array<String>) {
    val program = AstTranslator().visitProgram(parse(args[0]))
    println(CFG.toCfg(program))
    println(inline(program.block.stmts))
}
