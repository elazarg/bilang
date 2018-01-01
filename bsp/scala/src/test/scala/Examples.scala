
import Syntax._

object Examples {
  def reveal(role: Name, v: Name, c: Name): Public = {
    Public(v, where = BinOp(Op.EQ, Hash(Var(role, v)), Var(role, c)))
  }

  val oddsEvensRows = ProgramRows(
    Map("Odd" -> true, "Even" -> true),
    Seq(
      BigStep(
        action=Map(
          "Odd"  -> LocalStep(Public("ch")),
          "Even" -> LocalStep(Public("ch"))
        ),
        timeout=1,
        commands=Seq[Stmt]()
      ),
      BigStep(
        action=Map(
          "Odd" -> LocalStep(reveal("Odd", "c", "ch")),
          "Even" -> LocalStep(reveal("Even", "c", "ch"))
        ),
        timeout=1,
        commands=Seq[Stmt](
          Assign("Winner", BinOp(Op.EQ, Var("Odd", "c"), Var("Even", "c")))
        )
      )
    ))

  val oddsEvensCols = ProgramCols(
    Map(
      "Odd" -> (true, Seq(LocalStep(Public("ch")), LocalStep(reveal("Odd",  "c", "ch")))),
      "Even"-> (true, Seq(LocalStep(Public("ch")), LocalStep(reveal("Even", "c", "ch"))))
    ),
    Seq(1, 1), // FIX: no join timeout
    Seq(Seq(), Seq(Assign("Winner", BinOp(Op.EQ, Var("Odd", "c"), Var("Even", "c")))))
  )

  val alice: Agent = 0
  val bob: Agent = 1

  val packets = Seq(
    JoinPacket(alice, "Odd"),
    JoinPacket(bob, "Even"),
    ProgressPacket(),

    SmallStepPacket(alice, "Odd", Utils.hash(Num(0))),
    SmallStepPacket(bob, "Even", Utils.hash(Num(1))),
    ProgressPacket(),

    SmallStepPacket(alice, "Odd", Num(0)),
    SmallStepPacket(bob, "Even", Num(1)),
    ProgressPacket(),
  )
}
