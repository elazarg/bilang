
import Model.Event
import Syntax._

object OddsEvens extends Example {
  def reveal(role: Name, v: Name, c: Name): LocalStep = {
    LocalStep(
      Public(v, where = BinOp(Op.EQ, Hash(Var(role, v)), Var(role, c))),
      Fold(Seq(), Seq(Assign(Var(role, v),  Var(role, c))))
    )
  }

  private val odd: RoleName = "Odd"
  private val even: RoleName = "Even"
  private val global: RoleName = "Global"

  override val rows = ProgramRows(
    Map(odd -> true, even -> true),
    Seq(
      BigStep(
        action = Map(
          odd  -> singlePublic(odd, "ch"),
          even -> singlePublic(even, "ch"),
        ),
        timeout = 1,
        commands = Seq()
      ),
      BigStep(
        action = Map(
          odd -> reveal(odd, "c", "ch"),
          even -> reveal(even, "c", "ch")
        ),
        timeout = 1,
        commands = Seq(
          Assign(Var(global, "Winner"), BinOp(Op.EQ, Var(odd, "c"), Var(even, "c")))
        )
      )
    )
  )

  private def singlePublic(role: RoleName, name: Name): LocalStep =
    LocalStep(Public("ch"), Fold(Seq(), Seq(Assign(Var(role, name), Var(role, name)))))

  override val cols = ProgramCols(
    Map(
      odd  -> (true, Seq(singlePublic(odd,  "ch"), reveal(odd,  "c", "ch"))),
      even -> (true, Seq(singlePublic(even, "ch"), reveal(even, "c", "ch")))
    ),
    Seq(1, 1), // FIX: no join timeout
    Seq(Seq(), Seq(Assign(Var(global, "Winner"), BinOp(Op.EQ, Var(odd, "c"), Var(even, "c")))))
  )

  class Player(role: RoleName, n: Int) extends Strategy {
    override def act(events: List[Event]): Packet = events match {
      case List() => JoinPacket(this, -1, role)
      case List(_) => SmallStepPacket(this, 0, role, Utils.hash(Num(n)))
      case List(_, _) => SmallStepPacket(this, 1, role, Num(n))
      case List(_, _, _) => DisconnectPacket(this, 2, role)
    }
  }

  val players: List[Strategy] = List(new Player("Odd", 0), new Player("Even", 1))
}
