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

  private val commit = LocalStep(Some(Public("beth")))
  private val reveal = LocalStep(Some(Public("bet", where = BinOp(Op.EQ, Hash(Var("Player", "bet")), Var("Player", "beth")))), fold)
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

  class Player(n: Int) extends Strategy {
    override def act(events: List[Event]): Option[Packet] = Some(events match {
      case List() => JoinPacket(this, -1, "Player")
      case List(_) => SmallStepPacket(this, 0, "Player", Utils.hash(Num(n)))
      case List(_, _) => SmallStepPacket(this, 1, "Player", Num(n))
      case List(_, _, _) => DisconnectPacket(this, 2, "Player")
    })
  }

  val game: Game = SNPG
  val players: List[Strategy] = List(new Player(50), new Player(150))
  val schedule: List[Action] = List(
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
  )
  val expectedEvents = List(Map(), Map(), Map(Var("Global", "Payment") -> Num(100)))
}
