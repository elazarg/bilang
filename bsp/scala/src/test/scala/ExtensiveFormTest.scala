import org.scalatest.FunSuite
import Syntax._

class ExtensiveFormTest extends FunSuite {
  test("Extensive form of OddsEvens") {
    val res = ExtensiveNetwork.make(OddsEvens.rows)
    print(res)
  }
}
