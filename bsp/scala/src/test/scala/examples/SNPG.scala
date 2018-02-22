import Model.Event
import Syntax._

object SNPG extends Game {
  private val fold = Fold(
    inits = Seq(
      Assign(Var("Player", "S"), Num(0)),
      Assign(Var("Player", "Count"), Num(0))
    ),
    stmts = Seq(
      Assign(Var("Player", "S"), BinOp(Op.ADD, Var("Player", "S"), Var("Player", "bet"))),
      Assign(Var("Player", "Count"), BinOp(Op.ADD, Var("Player", "Count"), Num(1)))
    )
  )

  private val commit = LocalStep(Some(Action("bet", public=false)))
  private val reveal = LocalStep(Some(Action("bet", public=true)), fold)
  private val finalCommands = Seq(Assign(Var("Global", "Payment"), BinOp(Op.DIV, Var("Player", "S"), Var("Player", "Count"))))

  override val rows = ProgramRows(
    Map("Player" -> false),
    Seq(
      BigStep(action = Map("Player" -> commit), timeout = 1),
      BigStep(action = Map("Player" -> reveal), timeout = 1)
    ),
    finalCommands
  )

  override val cols = ProgramCols(
    Map("Player" -> (false, Seq(commit, reveal))),
    Seq(1, 1), // FIX: no join timeout
    finalCommands
  )
}

object SNPGRun extends GameRun {

  class Player(n: Int) extends SimpleStrategy {
    override val role = "Player"
    override def actSimple(events: List[Event]): Option[Value] =
      Some(events match {
        case List(_) => Utils.hash(Num(n))
        case List(_, _) => Num(n)
      })
  }

  val game: Game = SNPG
  val players: List[Strategy] = List(new Player(50), new Player(150))
  val schedule: List[Action] = List(
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
  )

  override val expectedEvents: List[StepState] =
    List(
      StepState(Map(),Map(players(1) -> Map(), players(0) -> Map())),
      StepState(Map(),Map(players(1) -> Map(Var("Player","bet") -> Num(-215980852)), players(0) -> Map(Var("Player","bet") -> Num(1749213749)))),
      StepState(Map(Var("Player","S") -> Num(200), Var("Player","Count") -> Num(2)),Map(players(1) -> Map(Var("Player","bet") -> Num(150)), players(0) -> Map(Var("Player","bet") -> Num(50))))
    )
}
