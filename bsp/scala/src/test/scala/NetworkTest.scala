import org.scalatest.FunSuite

class NetworkTest extends FunSuite {
  test("Odds and Evens happy path executes without errors") {
    runtest(OddsEvens)
  }
  test("SNPG happy path executes without errors") {
    runtest(SNPG)
  }

  private def runtest(ex: Example): Unit = {
    val model = new Model(ex.rows)
    val net = new Network(model, ex.players)

    def bigstep(): Unit = {
      net.clientStep(0);  net.clientStep(1)
      net.perform(0);     net.perform(1)
      net.AddProgress(0); net.perform(0)
    }
    bigstep()
    bigstep()
    bigstep()
  }
}
