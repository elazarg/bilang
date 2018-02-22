import org.scalatest.FunSuite
import Syntax._

class ExtensiveFormTest extends FunSuite {
  test("Extensive form of OddsEvensSimple") {
    val res = ExtensiveNetwork.make(OddsEvensSimple.rows)
    println(res)
    assert(res === Node("Even", 0, Map(
        Bool(true) -> Node("Odd", 0, Map(
          Bool(true) -> Leaf(Map("Odd" -> -1, "Even" -> 1)),
          Bool(false) -> Leaf(Map("Odd" -> 1, "Even" -> -1))
        )),
        Bool(false) -> Node("Odd", 0, Map(
          Bool(true) -> Leaf(Map("Odd" -> 1, "Even" -> -1)),
          Bool(false) -> Leaf(Map("Odd" -> -1, "Even" -> 1))
        ))
      ))
    )
    println("EFG 2 R \"Evens Odds\" { \"Even\" \"Odd\" }")
    println("\"\"")
    println()
    for (line <- ExtensiveNetwork.toEfg(res, List("Even", "Odd"))) {
      println(line)
    }
    println()
  }
}
