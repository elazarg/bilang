package bilang

import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain
import io.kotest.datatest.withData
import bilang.generated.BiLangLexer
import bilang.generated.BiLangParser
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.File
import java.nio.file.Paths

data class TestCase(
    val example: String,
    val extension: String,
    val backend: String,
    val generator: (ExpProgram) -> String
) {
    override fun toString() = "$example.$extension ($backend)"
}

class GoldenMasterTest : FreeSpec({

    val exampleFiles = listOf(
        "Bet",
        "MontyHall",
        "MontyHallChance",
        "OddsEvens",
        "OddsEvensShort",
        "Prisoners",
        "Simple",
        "Trivial1",
        "Puzzle",
        "ThreeWayLottery",
        "ThreeWayLotteryShort"
    )

    val testCases = exampleFiles.flatMap { example ->
        listOf(
            TestCase(example, "sol", "solidity") { prog -> genGame(prog) },
            TestCase(example, "efg", "gambit") { prog -> Extensive(prog).toEfg() },
            TestCase(example, "z3", "smt") { prog -> smt(prog) }
        )
    }

    "Golden Master Tests" - {
        "Test all examples against golden masters" - {
            withData(testCases) { testCase ->
                val goldenFile = getGoldenFile(testCase)

                try {
                    val actualOutput = generateOutput(testCase)
                    val sanitized = sanitizeOutput(actualOutput, testCase.backend)
                    if (!goldenFile.exists()) {
                        error("Missing golden file for $testCase.")
                    }
                    val expectedOutput = sanitizeOutput(goldenFile.readText(), testCase.backend)

                    val parent = "test-diffs/${testCase.backend}"
                    val diffFile = File("$parent/${testCase.example}.${testCase.extension}.diff")
                    val actualFile = File("$parent/${testCase.example}.${testCase.extension}")

                    if (sanitized != expectedOutput) {
                        // Write debug artifacts
                        diffFile.parentFile.mkdirs()
                        diffFile.writeText(computeDiff(expectedOutput, sanitized))
                        actualFile.writeText(sanitized)
                    } else {
                        // Clean up stale debug artifacts
                        // Note that untested artifacts would remain, whether stale or not
                        diffFile.delete()
                        actualFile.delete()
                    }
                    sanitized shouldBe expectedOutput

                } catch (e: NotImplementedError) {
                    // Skip test for unimplemented features
                    println("Skipped (not implemented): ${testCase.example}.${testCase.extension}")
                }
            }
        }
    }

    "Individual Backend Tests" - {

        "Solidity generation should be deterministic" {
            val example = "MontyHall"
            val program = parseExample(example)

            val output1 = genGame(program)
            val output2 = genGame(program)

            sanitizeOutput(output1, "solidity") shouldBe sanitizeOutput(output2, "solidity")
        }

        "Gambit generation should preserve game structure" {
            val program = parseExample("Prisoners")
            val efg = Extensive(program).toEfg()

            efg shouldContain "EFG 2 R"
        }

        "SMT generation should be valid SMT-LIB" {
            val program = parseExample("Simple")
            val smtOutput = smt(program)

            smtOutput shouldContain "(check-sat)"
            smtOutput shouldContain "(get-model)"
        }
    }
})

// === Helpers ===

private fun getGoldenFile(testCase: TestCase): File =
    File("examples/${testCase.backend}/${testCase.example}.${testCase.extension}")

private fun generateOutput(testCase: TestCase): String {
    val program = parseExample(testCase.example)
    return testCase.generator(program)
}

private fun parseExample(example: String): ExpProgram {
    val inputPath = Paths.get("examples/$example.bi")
    val chars = CharStreams.fromPath(inputPath)
    val tokens = CommonTokenStream(BiLangLexer(chars))
    val ast = BiLangParser(tokens).program()
    return AstTranslator().visitProgram(ast).copy(name = example, desc = example)
}

private fun sanitizeOutput(content: String, backend: String): String =
    when (backend) {
        "solidity" -> content
            .replace(Regex("lastBlock = block\\.timestamp;"), "lastBlock = TIMESTAMP;")
            .replace(Regex("block\\.timestamp"), "TIMESTAMP")
            .replace(Regex("//.*\\d{10,}.*\n"), "// TIMESTAMP_COMMENT\n")
            .replace(Regex("0x[0-9a-fA-F]{40}"), "0xADDRESS")
            .replace(Regex("\\s+\n"), "\n")
            .replace(Regex("\n{3,}"), "\n\n")
            .trim()

        "gambit" -> content
            .replace(Regex("\\b\\d{7,}\\b"), "HASH")
            .replace(Regex("\\d+\\.\\d{10,}"), "FLOAT")
            .trim()

        "smt" -> content
            .replace(Regex("_\\d{7,}"), "_HASH")
            .replace(Regex("\\s+\n"), "\n")
            .trim()

        else -> content.trim()
    }

private fun computeDiff(expected: String, actual: String): String {
    val expectedLines = expected.lines()
    val actualLines = actual.lines()
    val diff = StringBuilder()

    val maxLines = maxOf(expectedLines.size, actualLines.size)
    for (i in 0 until maxLines) {
        val e = expectedLines.getOrNull(i) ?: ""
        val a = actualLines.getOrNull(i) ?: ""
        if (e != a) {
            diff.appendLine("Line ${i + 1}:")
            if (e.isNotEmpty()) diff.appendLine("  - $e")
            if (a.isNotEmpty()) diff.appendLine("  + $a")
        }
    }
    return if (diff.isEmpty()) "No differences" else diff.toString()
}
