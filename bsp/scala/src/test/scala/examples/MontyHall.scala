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
    Assign(Var("Global", "Winner"), BinOp(Op.EQ, Var(host, "car"), Var(guest, "door2")))
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

  class PlayerHost(role: RoleName, car: Int) extends Strategy {
    override def act(events: List[Event]): Option[Packet] = events match {
      case List() => Some(JoinPacket(this, -1, role))
      case List(_) => Some(SmallStepPacket(this, 0, role, Utils.hash(Num(car))))
      case List(_, _) => None
      case List(_, _, m) =>
        val Num(door1) = m.static(Var("Guest", "door1"))
        val goat = chooseExcept(door1, car)
        Some(SmallStepPacket(this, 2, role, Num(goat)))
      case List(_, _, _, _) => None
      case List(_, _, _, _, _) => Some(SmallStepPacket(this, 4, role, Num(car)))
    }
  }

  class PlayerGuest(role: RoleName, door1: Int, switch: Boolean) extends Strategy {
    override def act(events: List[Event]): Option[Packet] = events match {
      case List() => Some(JoinPacket(this, -1, role))
      case List(_) => None
      case List(_, _) => Some(SmallStepPacket(this, 1, role, Num(door1)))
      case List(_, _, _) => None
      case List(_, _, _, m) =>
        val Num(goat) = m.static(Var("Host", "goat"))
        val door2 = if (switch) chooseExcept(goat, door1) else door1
        Some(SmallStepPacket(this, 3, role, Num(door2)))
      case List(_, _, _, _, _) => None
    }
  }

  val game: Game = MontyHall
  val players: List[Strategy] = List(new PlayerHost("Host", 0), new PlayerGuest("Guest", 0, true))
  val schedule: List[Action] = List(
    Send(0), Send(1), Deliver(0), Deliver(1), Progress(0), Deliver(0),

    Send(0), Deliver(0), Progress(0), Deliver(0), // carh
    Send(1), Deliver(1), Progress(1), Deliver(1), // door1
    Send(0), Deliver(0), Progress(0), Deliver(0), // goat
    Send(1), Deliver(1), Progress(1), Deliver(1), // door2
    Send(0), Deliver(0), Progress(0), Deliver(0), // car
  )
  val expectedEvents: List[Map[Var, Value]] = List(Map(), Map(), Map(Var("Global", "Winner") -> Bool(false)))
}
