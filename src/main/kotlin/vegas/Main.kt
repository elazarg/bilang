package vegas

import vegas.generated.VegasLexer
import vegas.generated.VegasParser
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.nio.file.Paths
import java.net.URI
import java.nio.file.Files
import java.nio.file.Path
import kotlin.system.exitProcess


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

    return AstTranslator(path.toUri()).visitProgram(ast)
}

private fun run(name: String) {
    val inputFilename = "examples/$name.vg"
    println("Analyzing $inputFilename ...")
    val program = parseFile(inputFilename).copy(name = name, desc = name)
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
    try {
        typeCheck(program)
    } catch (ex: NotImplementedError) {
        println(ex.message)
    } catch (ex: StaticError) {
        println("Type error: " + ex.message + " at " + ex.span())
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

private data class Outputs(
    val z3: Boolean,
    val efg: Boolean,
    val scr: Boolean,
    val sol: Boolean
)

private fun parseOutputs(flags: List<String>): Outputs {
    if (flags.isEmpty()) return Outputs(z3 = true, efg = true, scr = true, sol = true)

    var wantZ3 = false
    var wantEfg = false
    var wantScr = false
    var wantSol = false

    for (f in flags) {
        when (f.lowercase()) {
            "--z3" -> wantZ3 = true
            "--efg" -> wantEfg = true
            "--scr" -> wantScr = true
            "--sol" -> wantSol = true
            else -> throw IllegalArgumentException("Unknown flag: $f")
        }
    }

    // If the user provided any known flags, emit only those.
    val any = wantZ3 || wantEfg || wantScr || wantSol
    return if (any) Outputs(wantZ3, wantEfg, wantScr, wantSol)
    else Outputs(z3 = true, efg = true, scr = true, sol = true)
}

private fun runFile(inputPath: Path, outputs: Outputs) {
    require(Files.exists(inputPath)) { "Input file does not exist: $inputPath" }
    require(inputPath.toString().endsWith(".vg")) { "Expected a .vg file: $inputPath" }

    val baseName = inputPath.fileName.toString().removeSuffix(".vg")
    val outDir = inputPath.parent ?: Path.of(".")
    val outZ3 = outDir.resolve("$baseName.z3")
    val outEfg = outDir.resolve("$baseName.efg")
    val outScr = outDir.resolve("$baseName.scr")
    val outSol = outDir.resolve("$baseName.sol")

    println("Analyzing $inputPath ...")
    val program = parseFile(inputPath.toString()).copy(name = baseName, desc = baseName)

    println("roles: " + findRoles(program.game))
    doTypecheck(program)

    if (outputs.z3) writeFile(outZ3.toString()) { smt(program) }
    if (outputs.efg) writeFile(outEfg.toString()) { buildExtensiveFormGame(program).toEfg() }
    if (outputs.scr) writeFile(outScr.toString()) { programToScribble(program).prettyPrintAll() }
    if (outputs.sol) writeFile(outSol.toString()) { genGame(program) }

    println("Done")
    println()
}

fun main(args: Array<String>) {
    if (args.isEmpty()) {
        System.err.println(
            """
            Usage: vegas <path/to/file.vg> [--efg] [--z3] [--scr] [--sol]
            
            If no format flags are given, all outputs are generated alongside the input:
              - <file>.z3   (SMT)
              - <file>.efg  (Gambit EFG)
              - <file>.scr  (Scribble)
              - <file>.sol  (Solidity)
            """.trimIndent()
        )
        exitProcess(2)
    }

    val input = Path.of(args[0]).toAbsolutePath().normalize()
    val flags = args.drop(1)
    val outputs = try {
        parseOutputs(flags)
    } catch (e: IllegalArgumentException) {
        System.err.println("Error: ${e.message}")
        exitProcess(2)
    }

    try {
        runFile(input, outputs)
    } catch (e: Throwable) {
        System.err.println("Error: ${e.message}")
        e.printStackTrace()
        exitProcess(1)
    }
}
