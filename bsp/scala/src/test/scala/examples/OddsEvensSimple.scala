import Model.Event
import Syntax._

object OddsEvensSimple extends Game {
  def reveal(role: Name): LocalStep = {
    LocalStep(Some(Public("c")), Fold(Seq(), Seq(Assign(Var(role, "c"), Var(role, "c")))))
  }

  private val odd: RoleName = "Odd"
  private val even: RoleName = "Even"
  private val finalCommands = Seq(
    Assign(Var(even, "Prize"), IfThenElse(BinOp(Op.EQ, Var(odd, "c"), Var(even, "c")), Num(1), Num(-1))),
    Assign(Var(odd, "Prize"), IfThenElse(BinOp(Op.EQ, Var(odd, "c"), Var(even, "c")), Num(-1), Num(1)))
  )

  private val oddReveal: LocalStep = reveal(odd)
  private val evenReveal: LocalStep = reveal(even)

  override val rows = ProgramRows(
    Map(odd -> true, even -> true),
    Seq(
      BigStep(Map(even -> evenReveal, odd -> oddReveal), 1)
    ),
    finalCommands
  )

  override val cols = ProgramCols(
    Map(
      even -> (true, Seq(evenReveal)),
      odd -> (true, Seq(oddReveal))
    ),
    Seq(1, 1), // FIX: no join timeout
    finalCommands
  )
}

object OddsEvensSimpleRun extends GameRun {
  class Player(override val role: RoleName, n: Int) extends SimpleStrategy {
    override def actSimple(events: List[Event]): Option[Value] =
      Some(events match {
        case List(_, _) => Num(n)
      })
  }

  val game: Game = OddsEvens
  private val odd = new Player("Odd", 0)
  private val even = new Player("Even", 1)
  val players: List[Strategy] = List(odd, even)
  val schedule: List[Action] = List( // TODO: make progress decision part of the strategy
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
  )
  override val expectedEvents: List[StepState] =
    List(
      StepState(
        static=Map(),
        objects=Map(odd -> Map(), even -> Map())
      ),
      StepState(
        static=Map(Var("Odd","c") -> Num(0), Var("Even","c") -> Num(1)),
        objects=Map(odd -> Map(Var("Odd","c") -> Num(0)), even -> Map(Var("Even","c") -> Num(1)))
      )
    )
}
