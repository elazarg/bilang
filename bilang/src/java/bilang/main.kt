package bilang

import java.nio.file.Paths

import org.antlr.v4.runtime.*

import bilang.generated.*

fun parse(inputFilename: String): Program =
        AstTranslator().visitProgram(BiLangParser(CommonTokenStream(BiLangLexer(CharStreams.fromPath(Paths.get(inputFilename))))).program())

fun main(args: Array<String>) {
    val program = parse("examples/ThreeWayLottery.bi")
    val p = inline(inlineWhere(program))
    println(prettyPrint(p))
}
