import Model.Event
import Syntax._

object SNPG extends Example {
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

  private val commit = LocalStep(Public("beth"))
  private val reveal = LocalStep(Public("bet", where = BinOp(Op.EQ, Hash(Var("Player", "bet")), Var("Player", "beth"))), fold)
  private val payment = Assign(Var("Global", "Payment"), BinOp(Op.DIV, Var("Player", "S"), Var("Player", "Count")))

  override val rows = ProgramRows(
    Map("Player" -> false),
    Seq(
      BigStep(action = Map("Player" -> commit), timeout = 1, commands = Seq()),
      BigStep(action = Map("Player" -> reveal), timeout = 1, commands = Seq(payment))
    )
  )

  override val cols = ProgramCols(
    Map("Player" -> (false, Seq(commit, reveal))),
    Seq(1, 1), // FIX: no join timeout
    Seq(Seq(), Seq(payment))
  )

  class Player(n: Int) extends Strategy {
    override def act(events: List[Event]): Packet = events match {
      case List() => JoinPacket(this, -1, "Player")
      case List(_) => SmallStepPacket(this, 0, "Player", Utils.hash(Num(n)))
      case List(_, _) => SmallStepPacket(this, 1, "Player", Num(n))
      case List(_, _, _) => DisconnectPacket(this, 2, "Player")
    }
  }

  val players = List(new Player(50), new Player(150))
}
