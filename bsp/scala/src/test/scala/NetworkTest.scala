import org.scalatest.FunSuite

class NetworkTest extends FunSuite {

  test("Odds and Evens happy path executes without errors") {
    runtest(OddsEvensRun)
  }

  test("SNPG happy path executes without errors") {
    runtest(SNPGRun)
  }

  test("MontyHall happy path executes without errors") {
    runtest(MontyHallRun)
  }

  test("Auction happy path executes without errors") {
    runtest(AuctionRun)
  }

  private def runtest(run: GameRun): Unit = {
    val model = new Model(run.game.rows)
    val net = new Network(model, run.players)
    run.schedule.foreach {
      case Send(i) => net.clientStep(i)
      case Progress(i) => net.AddProgress(i)
      case Deliver(i) => net.perform(i)
    }
    assert(net.events === run.expectedEvents)
  }
}
