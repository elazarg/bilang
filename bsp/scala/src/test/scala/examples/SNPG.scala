import Syntax._

object SNPG extends Example {
  def reveal(role: Name, v: Name, c: Name): Public = {
    Public(v, where = BinOp(Op.EQ, Hash(Var(role, v)), Var(role, c)))
  }

  override val cols = ProgramCols(
    Map(
      "Player" -> (false,
        Seq(LocalStep(Public("beth")),
            LocalStep(
              reveal("Player", "bet", "beth"),
              Fold(Seq(
                Assign(Var("Glboal", "S"),     BinOp(Op.ADD, Var("Global", "S"),     Var("Player", "bet"))),
                Assign(Var("Glboal", "Count"), BinOp(Op.ADD, Var("Global", "Count"), Num(1)))
              ))
            )
      )
      ),
    ),
    Seq(1, 1), // FIX: no join timeout
    Seq(Seq(Assign(Var("Glboal", "S"), Num(0)),
            Assign(Var("Glboal", "Count"), Num(0))),
        Seq(Assign(Var("Glboal", "Payment"), BinOp(Op.DIV, Var("Global", "S"), Var("Global", "Count"))))
    )
  )

  val alice: Agent = 0
  val bob: Agent = 1

  val packets = Seq(
    JoinPacket(alice, "Player"),
    JoinPacket(bob,   "Player"),
    ProgressPacket(),

    SmallStepPacket(alice, "Player", Utils.hash(Num(50)) ),
    SmallStepPacket(bob,   "Player", Utils.hash(Num(150))),
    ProgressPacket(),

    SmallStepPacket(alice, "Player", Num(50) ),
    SmallStepPacket(bob,   "Player", Num(150)),
    ProgressPacket(),
  )
}
