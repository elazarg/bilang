import org.scalatest.FunSuite
import Syntax._

class ExtensiveFormTest extends FunSuite {
  test("Extensive form of OddsEvensSimple") {
    val res = ExtensiveNetwork.make(OddsEvensSimple.rows)
    assert(res === List(
      "EFG 2 R \"Odds and Evens game\" { \"Odd\" \"Even\" }",
      "\"\"",
      "",
      "p \"\" 2 1 \"\" { \"1\" \"2\" } 0",
      "p \"\" 1 1 \"\" { \"1\" \"2\" } 0",
      "t \"\" 1 \"\" { -1, 1 }",
      "t \"\" 2 \"\" { 1, -1 }",
      "p \"\" 1 1 \"\" { \"1\" \"2\" } 0",
      "t \"\" 3 \"\" { 1, -1 }",
      "t \"\" 4 \"\" { -1, 1 }"
    ))
    println(res.mkString("\n"))
  }
  test("Extensive form of MontyHall") {
    val res = ExtensiveNetwork.make(MontyHall.rows)
    println(res.mkString("\n"))
  }
}
