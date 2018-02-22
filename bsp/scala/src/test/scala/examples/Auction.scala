import Model.Event
import Syntax._

object Auction extends Game {
  private val highest = Var("Bidder", "highest")
  private val offer = Var("Bidder", "offer")
  private val minimal = Num(15) // TODO: in-game decision

  private val fold = Fold(
    inits = Seq(
      Assign(highest, minimal),
    ),
    stmts = Seq(
      Assign(highest, IfThenElse(BinOp(Op.LT, highest, offer), offer, highest)),
    )
  )

  private val commit = LocalStep(Some(Action("offer", public=false)))
  private val reveal = LocalStep(Some(Action("offer", public=true)), fold)
  private val finalCommands = Seq(Assign(Var("Global", "Highest"), highest))

  override val rows = ProgramRows(
    Map("Bidder" -> false),
    Seq(
      BigStep(action = Map("Bidder" -> commit), timeout = 1),
      BigStep(action = Map("Bidder" -> reveal), timeout = 1)
    ),
    finalCommands
  )

  override val cols = ProgramCols(
    Map("Bidder" -> (false, Seq(commit, reveal))),
    Seq(1, 1), // FIX: no join timeout
    finalCommands
  )
}

object AuctionRun extends GameRun {

  class Bidder(offer: Int) extends SimpleStrategy {
    override val role = "Bidder"
    override def actSimple(events: List[Event]): Option[Value] =
      Some(events match {
        case List(_) => Utils.hash(Num(offer))
        case List(_, _) => Num(offer)
      })
  }

  val game: Game = Auction
  val players: List[Strategy] = List(new Bidder(50), new Bidder(150), new Bidder(72))
  val schedule: List[Action] = List(
    Send(0), Send(1), Send(2), Deliver(0), Deliver(1), Deliver(2), Progress(0), Deliver(0),
    Send(0), Send(1), Send(2), Deliver(0), Deliver(1), Deliver(2), Progress(0), Deliver(0),
    Send(0), Send(1), Send(2), Deliver(0), Deliver(1), Deliver(2), Progress(0), Deliver(0),
  )
  override val expectedEvents: List[StepState] =
    List(
      StepState(Map(),Map(players(2)-> Map(), players(1) -> Map(), players(0) -> Map())),
      StepState(Map(),Map(players(2)-> Map(Var("Bidder","offerh") -> Num(-1743610656)), players(1) -> Map(Var("Bidder","offerh") -> Num(-215980852)), players(0) -> Map(Var("Bidder","offerh") -> Num(1749213749)))),
      StepState(Map(Var("Bidder","highest") -> Num(150)),Map(players(2)-> Map(Var("Bidder","offer") -> Num(72)), players(1) -> Map(Var("Bidder","offer") -> Num(150)), players(0) -> Map(Var("Bidder","offer") -> Num(50))))
    )
}
