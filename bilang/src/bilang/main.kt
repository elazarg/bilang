package bilang

import generated.BiLangLexer
import generated.BiLangParser
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.nio.file.Paths

fun parse(inputFilename: String): ExpProgram {
    val chars = CharStreams.fromPath(Paths.get(inputFilename))
    val tokens = CommonTokenStream(BiLangLexer(chars))
    val ast = BiLangParser(tokens).program()
    return AstTranslator().visitProgram(ast)
}

private fun run(name: String) {
    val inputFilename = "examples/$name.bi"
    println("Analyzing $inputFilename ...")
    val program = parse(inputFilename).copy(desc=name)
    writeFile("examples/gambit/$name.efg", Extensive(name, program).toEfg())
    writeFile("examples/scribble/$name.scr", programToScribble(program).prettyPrintAll())
    writeFile("examples/solidity/$name.sol", genGame(program))
    println("Done")
    println()
}

private fun writeFile(filename: String, text: String) {
    print("Writing file $filename... ")
    Paths.get(filename).toFile().writeText(text)
    println("Done")
}

fun main(args: Array<String>) {
    run("Puzzle")
    run("MontyHall")
    run("OddsEvens")
    run("ThreeWayLottery")
}
