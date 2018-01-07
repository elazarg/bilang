import org.scalatest.FunSuite

class NetworkTest extends FunSuite {
  test("Odds and Evens happy path executes without errors") {
    runtest(OddsEvens)
  }
  test("SNPG happy path executes without errors") {
    runtest(SNPG)
  }

  private def runtest(ex: Example): Unit = {
    val net = new Network(new Model(ex.rows), ex.players)

    net.clientStep(0);  net.clientStep(1)
    net.perform(0);     net.perform(1)
    net.AddProgress(0); net.perform(0)

    net.clientStep(0);  net.clientStep(1)
    net.perform(0);     net.perform(1)
    net.AddProgress(0); net.perform(0)
  }
}
