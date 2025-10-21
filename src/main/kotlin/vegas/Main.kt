package vegas

import vegas.generated.VegasLexer
import vegas.generated.VegasParser
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.nio.file.Paths
import java.net.URI

fun parseCode(code: String, uri: URI = URI.create("inmemory:repl.vg")): ExpProgram {
    // Ensure there's always a withdraw statement
    val fullCode = if (!code.contains("withdraw")) "$code; withdraw {}" else code

    // Give ANTLR a source name that matches the URI (helps error messages)
    val chars = CharStreams.fromString(fullCode, uri.toString())
    val tokens = CommonTokenStream(VegasLexer(chars))
    val ast = VegasParser(tokens).program()

    return AstTranslator(uri).visitProgram(ast)
}

fun parseFile(inputFilename: String): ExpProgram {
    val path = Paths.get(inputFilename)
    val chars = CharStreams.fromPath(path) // source name = path.toString()
    val tokens = CommonTokenStream(VegasLexer(chars))
    val ast = VegasParser(tokens).program()

    return AstTranslator( path.toUri()).visitProgram(ast)
}

private fun run(name: String) {
    val inputFilename = "examples/$name.vg"
    println("Analyzing $inputFilename ...")
    val program = parseFile(inputFilename).copy(name=name, desc=name)
    println("roles: " + findRoles(program.game))
    doTypecheck(program)
    writeFile("examples/smt/$name.z3") { smt(program) }
    writeFile("examples/gambit/$name.efg") { buildExtensiveFormGame(program).toEfg() }
    writeFile("examples/scribble/$name.scr") { programToScribble(program).prettyPrintAll() }
    writeFile("examples/solidity/$name.sol") { genGame(program) }
    println("Done")
    println()
}

private fun doTypecheck(program: ExpProgram) {
    print("Type checking file ... ")
    try {
        typeCheck(program)
        println("done")
    } catch (ex: NotImplementedError) {
        println(ex.message)
    } catch (ex: StaticError) {
        println("Type error: " + ex.message)
    }
}

private fun writeFile(filename: String, f: () -> String) {
    print("Writing file $filename... ")
    try {
        val text = f()
        Paths.get(filename).toFile().writeText(text)
    } catch (ex: NotImplementedError) {
        println(ex.message)
    }
    println("Done")
}

fun main(args: Array<String>) {
    listOf(
            "Bet",
            "Trivial1",
            "Simple",
            "Puzzle",
            "MontyHall", "MontyHallChance",
            "OddsEvens", "OddsEvensShort",
            "Prisoners",
            "ThreeWayLottery", "ThreeWayLotteryBuggy", "ThreeWayLotteryShort"
            // ,"TicTacToe"
    ).forEach { run(it) }
}
