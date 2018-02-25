import org.scalatest.FunSuite
import Syntax._

class ExtensiveFormTest extends FunSuite {
  test("MontyHall") {
    val doorVals = List(Num(1), Num(2), Num(3))
    val types = Map(
      Var("Guest", "door1") -> doorVals,
      Var("Guest", "door2") -> doorVals,
      Var("Host", "goat") -> doorVals,
      Var("Host", "car") -> doorVals
    )
    val res = new ExtensiveNetwork(types).make(MontyHall.rows)
    println(res.mkString("\n"))
  }
  test("ThreeWayLottery") {
    println()
    val opts = List(Num(1), Num(2), Num(3))
    val types = Map(
      Var("Issuer", "c") -> opts,
      Var("Alice", "c") -> opts,
      Var("Bob", "c") -> opts
    )
    val res = new ExtensiveNetwork(types).make(ThreeWayLottery.rows)
    println(res.mkString("\n"))
    println()
  }
  test("OddsEvensSimple") {
    val res = new ExtensiveNetwork().make(OddsEvensSimple.rows)
    println(res.mkString("\n"))
  }
  test("OddsEvens") {
    val res = new ExtensiveNetwork().make(OddsEvens.rows)
    println(res.mkString("\n"))
  }
}
