
import Model.Event
import Syntax._

object OddsEvens extends Game {
  def reveal(role: Name, v: Name, c: Name): LocalStep = {
    LocalStep(
      Some(Public(v, where = BinOp(Op.EQ, Hash(Var(role, v)), Var(role, c)))),
      Fold(Seq(), Seq(Assign(Var(role, v), Var(role, c))))
    )
  }

  private val odd: RoleName = "Odd"
  private val even: RoleName = "Even"
  private val finalCommands = Seq(
    Assign(Var("Global", "Winner"), BinOp(Op.EQ, Var(odd, "c"), Var(even, "c")))
  )

  private def singlePublic(role: RoleName) =
    LocalStep(Some(Public("ch")), Fold(Seq(), Seq(Assign(Var(role, "ch"), Var(role, "ch")))))

  private val oddCh: LocalStep = singlePublic(odd)
  private val evenCh: LocalStep = singlePublic(even)
  private val oddReveal: LocalStep = reveal(odd, "c", "ch")
  private val evenReveal: LocalStep = reveal(even, "c", "ch")

  override val rows = ProgramRows(
    Map(odd -> true, even -> true),
    Seq(
      BigStep(Map(odd -> oddCh, even -> evenCh), 1),
      BigStep(Map(odd -> oddReveal, even -> evenReveal), 1, finalCommands)
    )
  )

  override val cols = ProgramCols(
    Map(
      odd -> (true, Seq(oddCh, oddReveal)),
      even -> (true, Seq(evenCh, evenReveal))
    ),
    Seq(1, 1), // FIX: no join timeout
    Seq(Seq(), finalCommands)
  )
}

object OddsEvensRun extends GameRun {
  class Player(role: RoleName, n: Int) extends Strategy {
    override def act(events: List[Event]): Option[Packet] = Some(events match {
      case List() => JoinPacket(this, -1, role)
      case List(_) => SmallStepPacket(this, 0, role, Utils.hash(Num(n)))
      case List(_, _) => SmallStepPacket(this, 1, role, Num(n))
      case List(_, _, _) => DisconnectPacket(this, 2, role)
    })
  }

  val game: Game = OddsEvens
  val players: List[Strategy] = List(new Player("Odd", 0), new Player("Even", 1))
  val schedule: List[Action] = List( // TODO: make progress decision part of the strategy
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
  )
  val expectedEvents: List[Map[Var, Value]] = List(Map(), Map(), Map(Var("Global", "Winner") -> Bool(false)))
}
