import Model.Event
import Syntax._

object MontyHall extends Game {
  def reveal(role: Name, v: Name, c: Name): LocalStep = {
    LocalStep(
      Some(Public(v, where = BinOp(Op.EQ, Hash(Var(role, v)), Var(role, c)))),
      Fold(Seq(), Seq(Assign(Var(role, v), Var(role, c))))
    )
  }

  private val host: RoleName = "Host"
  private val guest: RoleName = "Guest"
  private val finalCommands = Seq(
    Assign(Var("Global", "Car"), Var(host, "car")),
    Assign(Var("Guest", "Prize"), IfThenElse(BinOp(Op.EQ, Var(host, "car"), Var(guest, "door2")), Num(1), Num(0)))
  )

  private def singlePublic(role: RoleName, v: Name, where : Exp = Bool(true)) =
    LocalStep(Some(Public(v, where)), Fold(Seq(), Seq(Assign(Var(role, v), Var(role, v)))))

  private val hostCarh: LocalStep = singlePublic(host, "carh")
  private val guestDoor1: LocalStep = singlePublic(guest, "door1")
  private val hostGoat: LocalStep = singlePublic(host, "goat", where = UnOp(Op1.NOT, BinOp(Op.EQ, Var("Host", "goat"), Var("Guest", "door1"))))
  private val guestDoor2: LocalStep = singlePublic(guest, "door2")
  private val hostReveal: LocalStep = reveal(host, "car", "carh")

  private val NOP = LocalStep(None, Fold(Seq(), Seq()))
  override val rows = ProgramRows(
    Map(host -> true, guest -> true),
    Seq(
      BigStep(Map(host -> hostCarh, guest -> NOP), 1),
      BigStep(Map(host -> NOP, guest -> guestDoor1), 1),
      BigStep(Map(host -> hostGoat, guest -> NOP), 1),
      BigStep(Map(host -> NOP, guest -> guestDoor2), 1),
      BigStep(Map(host -> hostReveal, guest -> NOP), 1)
    ),
    finalCommands
  )

  override val cols = ProgramCols(
    Map(
      host -> (true, Seq(hostCarh, NOP, hostGoat, hostReveal)),
      guest -> (true, Seq(NOP, guestDoor1, NOP, guestDoor2, NOP))
    ),
    Seq(1, 1), // FIX: no join timeout
    finalCommands
  )
}

object MontyHallRun extends GameRun {
  private val doors = Set(0, 1, 2)
  def chooseExcept(d1: Int, d2: Int): Int = new util.Random(15).shuffle(doors -- Set(d1, d2)).head

  class PlayerHost(override val role: RoleName, car: Int) extends SimpleStrategy {
    override def actSimple(events: List[Event]): Option[Value] = events match {
      case List(_) => Some(Utils.hash(Num(car)))
      case List(_, _) => None
      case List(_, _, env) =>
        val Num(door1) = env.static(Var("Guest", "door1"))
        val goat = chooseExcept(door1, car)
        Some(Num(goat))
      case List(_, _, _, _) => None
      case List(_, _, _, _, _) => Some(Num(car))
    }
  }

  class PlayerGuest(override val role: RoleName, door1: Int, switch: Boolean) extends SimpleStrategy {
    override def actSimple(events: List[Event]): Option[Value] = events match {
      case List(_) => None
      case List(_, _) => Some(Num(door1))
      case List(_, _, _) => None
      case List(_, _, _, env) =>
        val Num(goat) = env.static(Var("Host", "goat"))
        val door2 = if (switch) chooseExcept(goat, door1) else door1
        Some(Num(door2))
      case List(_, _, _, _, _) => None
    }
  }

  val game: Game = MontyHall
  private val host = new PlayerHost("Host", 0)
  private val guest = new PlayerGuest("Guest", 0, true)
  val players: List[Strategy] = List(host, guest)
  val schedule: List[Action] = List(
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),

    Send(0), Deliver(0), Progress(0), Deliver(0), // carh
    Send(1), Deliver(1), Progress(1), Deliver(1), // door1
    Send(0), Deliver(0), Progress(0), Deliver(0), // goat
    Send(1), Deliver(1), Progress(1), Deliver(1), // door2
    Send(0), Deliver(0), Progress(0), Deliver(0), // car
  )
  override val expectedEvents: List[StepState] =
    List(
      StepState(Map(),Map(host -> Map(), guest -> Map())),
      StepState(Map(Var("Host","carh") -> Num(-1669410282)),Map(host -> Map(Var("Host","carh") -> Num(-1669410282)), guest -> Map())),
      StepState(Map(Var("Guest","door1") -> Num(0)),Map(host -> Map(), guest -> Map(Var("Guest","door1") -> Num(0)))),
      StepState(Map(Var("Host","goat") -> Num(1)),Map(host -> Map(Var("Host","goat") -> Num(1)), guest -> Map())),
      StepState(Map(Var("Guest","door2") -> Num(2)),Map(host -> Map(), guest -> Map(Var("Guest","door2") -> Num(2)))),
      StepState(Map(Var("Host","car") -> Num(-1669410282)),Map(host -> Map(Var("Host","car") -> Num(0)), guest -> Map()))
    )
}
