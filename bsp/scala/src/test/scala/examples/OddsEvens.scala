
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
      odd -> (true, Seq(singlePublic(odd, "ch"),   reveal(odd, "c", "ch"))),
      even -> (true, Seq(singlePublic(even, "ch"), reveal(even, "c", "ch")))
    ),
    Seq(1, 1), // FIX: no join timeout
    Seq(Seq(), Seq(Assign(Var(global, "Winner"), BinOp(Op.EQ, Var(odd, "c"), Var(even, "c")))))
  )

  val alice: Agent = 0
  val bob: Agent = 1

  val packets = Seq(
    JoinPacket(alice, odd),
    JoinPacket(bob, even),
    ProgressPacket(),

    SmallStepPacket(alice, odd, Utils.hash(Num(0))),
    SmallStepPacket(bob, even, Utils.hash(Num(1))),
    ProgressPacket(),

    SmallStepPacket(alice, odd, Num(0)),
    SmallStepPacket(bob, even, Num(1)),
    ProgressPacket(),
  )
}
