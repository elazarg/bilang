import org.scalatest.FunSuite

class NetworkTest extends FunSuite {
  test("test network") {
    new Network(new Model(Examples.oddsEvensRows)).run(Examples.packets)
  }
}
