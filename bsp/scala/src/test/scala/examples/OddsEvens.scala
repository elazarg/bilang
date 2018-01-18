
import Model.Event
import Syntax._

object OddsEvens extends Game {
  def reveal(role: Name): LocalStep = {
    LocalStep(
      Some(Public("c", where = BinOp(Op.EQ, Hash(Var(role, "c")), Var(role, "ch")))),
      Fold(Seq(), Seq(Assign(Var(role, "c"), Var(role, "ch"))))
    )
  }

  private val odd: RoleName = "Odd"
  private val even: RoleName = "Even"
  private val finalCommands = Seq(
    Assign(Var("Global", "Winner"), BinOp(Op.EQ, Var(odd, "ch"), Var(even, "ch")))
  )

  private def singlePublic(role: RoleName) =
    LocalStep(Some(Public("ch")), Fold(Seq(), Seq(Assign(Var(role, "ch"), Var(role, "ch")))))

  private val oddCh: LocalStep = singlePublic(odd)
  private val evenCh: LocalStep = singlePublic(even)
  private val oddReveal: LocalStep = reveal(odd)
  private val evenReveal: LocalStep = reveal(even)

  override val rows = ProgramRows(
    Map(odd -> true, even -> true),
    Seq(
      BigStep(Map(odd -> oddCh, even -> evenCh), 1),
      BigStep(Map(odd -> oddReveal, even -> evenReveal), 1)
    ),
    finalCommands
  )

  override val cols = ProgramCols(
    Map(
      odd -> (true, Seq(oddCh, oddReveal)),
      even -> (true, Seq(evenCh, evenReveal))
    ),
    Seq(1, 1), // FIX: no join timeout
    finalCommands
  )
}

object OddsEvensRun extends GameRun {
  class Player(override val role: RoleName, n: Int) extends SimpleStrategy {
    override def actSimple(events: List[Event]): Option[Value] =
      Some(events match {
        case List(_) => Utils.hash(Num(n))
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
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
  )
  override val expectedEvents: List[StepState] =
    List(
      StepState(Map(),Map(odd -> Map(), even -> Map())),
      StepState(Map(Var("Even","ch") -> Num(818387364), Var("Odd","ch") -> Num(-1669410282)),Map(odd -> Map(Var("Odd","ch") -> Num(-1669410282)), even -> Map(Var("Even","ch") -> Num(818387364)))),
      StepState(Map(Var("Odd","c") -> Num(-1669410282), Var("Even","c") -> Num(818387364)),Map(odd -> Map(Var("Odd","c") -> Num(0)), even -> Map(Var("Even","c") -> Num(1))))
    )
    //List(Map(), Map(), Map(Var("Global", "Winner") -> Bool(false)))
}
