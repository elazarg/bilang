import Model.Event
import Syntax._

object ThreeWayLottery extends Game {
  def reveal(role: Name): LocalStep = {
    LocalStep(
      Some(Action("c", public=true)),
      Fold(Seq(), Seq(Assign(Var(role, "c"), Var(role, "c"))))
    )
  }

  private val issuer: RoleName = "Issuer"
  private val alice: RoleName = "Alice"
  private val bob: RoleName = "Bob"


  private val s = Var("Global", "sum")
  private val s1 = Var("Global", "sum1")
  private val w = Var("Global", "Winner")
  private val ic = Var(issuer, "c")
  private val ac = Var(alice, "c")
  private val bc = Var(bob, "c")
  private def coerce(v: Var) = Assign(v, IfThenElse(BinOp(Op.EQ, v, ImOut()), Num(0), v))
  private def zero(v: Var) = BinOp(Op.EQ, v, Num(0))
  private def prize(name: RoleName, n: Int) = Assign(Var(name, "Prize"), IfThenElse(BinOp(Op.EQ, w, Num(n)), Num(3), Num(-1)))

  private val finalCommands = Seq(
    coerce(ic), coerce(ac), coerce(bc),
    Assign(s, BinOp(Op.ADD, ic, BinOp(Op.ADD, ac, bc))),
    Assign(s1, BinOp(Op.MUL, BinOp(Op.DIV, s, Num(3)), Num(3))),
    Assign(w,
      IfThenElse(BinOp(Op.OR, zero(ac), zero(bc)), Num(0),
        IfThenElse(zero(ic), Num(1),
          IfThenElse(BinOp(Op.EQ, s1, s), Num(1),
            IfThenElse(BinOp(Op.EQ, s1, BinOp(Op.SUB, s, Num(1))), Num(2), Num(0))
          )
        )
      )
    ),
    prize(issuer, 0),
    prize(alice, 1),
    prize(bob, 2)
  )

  private def singleAction(role: RoleName, public: Boolean = true) =
    LocalStep(Some(Action("c", public)), Fold(Seq(), Seq(Assign(Var(role, "c"), Var(role, "c")))))

  private val issuerCh: LocalStep = singleAction(issuer, public=false)
  private val aliceCh: LocalStep = singleAction(alice, public=false)
  private val bobCh: LocalStep = singleAction(bob, public=false)
  private val issuerReveal: LocalStep = reveal(issuer)
  private val aliceReveal: LocalStep = reveal(alice)
  private val bobReveal: LocalStep = reveal(bob)

  override val rows = ProgramRows(
    Map(issuer -> true, alice -> true, bob -> true),
    Seq(
      BigStep(Map(issuer -> issuerCh, alice -> aliceCh, bob -> bobCh), 1),
      BigStep(Map(issuer -> issuerReveal, alice -> aliceReveal, bob -> bobReveal), 1)
    ),
    finalCommands
  )

  override val cols = ProgramCols(
    Map(
      issuer -> (true, Seq(issuerCh, issuerReveal)),
      alice -> (true, Seq(aliceCh, aliceReveal)),
      bob -> (true, Seq(bobCh, bobReveal))
    ),
    Seq(1, 1), // FIX: no join timeout
    finalCommands
  )
}

object ThreeWayLotteryRun extends GameRun {
  class Player(override val role: RoleName, n: Int) extends SimpleStrategy {
    override def actSimple(events: List[Event]): Option[Value] =
      Some(events match {
        case List(_) => Utils.hash(Num(n))
        case List(_, _) => Num(n)
      })
  }

  val game: Game = ThreeWayLottery
  private val issuer = new Player("Issuer", 0)
  private val alice = new Player("Alice", 1)
  private val bob = new Player("Bob", 1)
  val players: List[Strategy] = List(issuer, alice, bob)
  val schedule: List[Action] = List( // TODO: make progress decision part of the strategy
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),
  )
  override val expectedEvents: List[StepState] =
    List(
      StepState(Map(),Map(issuer -> Map(), alice -> Map())),
      StepState(Map(Var("Alice","c") -> Num(818387364), Var("Issuer","c") -> Num(-1669410282)),Map(issuer -> Map(Var("Issuer","c") -> Num(-1669410282)), alice -> Map(Var("Alice","c") -> Num(818387364)))),
      StepState(Map(Var("Issuer","c") -> Num(-1669410282), Var("Alice","c") -> Num(818387364)),Map(issuer -> Map(Var("Issuer","c") -> Num(0)), alice -> Map(Var("Alice","c") -> Num(1))))
    )
}
