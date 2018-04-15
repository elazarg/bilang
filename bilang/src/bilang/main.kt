package bilang

import java.nio.file.Paths

import org.antlr.v4.runtime.*

import generated.*

fun parse(inputFilename: String): ExpProgram =
        AstTranslator().visitProgram(BiLangParser(CommonTokenStream(BiLangLexer(CharStreams.fromPath(Paths.get(inputFilename))))).program())

fun main(args: Array<String>) {
    val program = parse("examples/MontyHall.bi")
    println(program)
}
