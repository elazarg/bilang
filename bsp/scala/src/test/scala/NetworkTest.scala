import org.scalatest.FunSuite

class NetworkTest extends FunSuite {
  test("Odds and Evens happy path executes without errors") {
    runtest(OddsEvens)
  }
  test("SNPG happy path executes without errors") {
    runtest(SNPG)
  }

  private def runtest(ex: Example): Unit = {
    new Network(new Model(ex.rows)).run(ex.packets)
  }
}
