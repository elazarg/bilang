import org.scalatest.FunSuite
import Syntax._

class ExtensiveFormTest extends FunSuite {
  test("MontyHall") {
    val res = ExtensiveNetwork.make(MontyHall.rows)
    println(res.mkString("\n"))
  }
  test("OddsEvensSimple") {
    val res = ExtensiveNetwork.make(OddsEvensSimple.rows)
    println(res.mkString("\n"))
  }
  test("OddsEvens") {
    val res = ExtensiveNetwork.make(OddsEvens.rows)
    println(res.mkString("\n"))
  }
}
