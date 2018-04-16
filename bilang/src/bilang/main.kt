package bilang

import java.nio.file.Paths

import org.antlr.v4.runtime.*

import generated.*
import java.io.File

fun parse(inputFilename: String): ExpProgram =
        AstTranslator().visitProgram(BiLangParser(CommonTokenStream(BiLangLexer(CharStreams.fromPath(Paths.get(inputFilename))))).program())

fun main(args: Array<String>) {
    val name = "MontyHall"
    val program = parse("examples/$name.bi")
    println(program)
    val extensive = Extensive(name, program)
    println(extensive)
    File("examples/$name.efg").writeText(extensive.toEfg())
}
