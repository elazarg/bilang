
import Syntax._

object OddsEvens extends Example {
  def reveal(role: Name, v: Name, c: Name): LocalStep = {
    LocalStep(
      Public(v, where = BinOp(Op.EQ, Hash(Var(role, v)), Var(role, c))),
      Fold(Seq(Assign(Var(role, v),  Var(role, c))))
    )
  }

  override val rows = ProgramRows(
    Map("Odd" -> true, "Even" -> true),
    Seq(
      BigStep(
        action = Map(
          "Odd" -> LocalStep(Public("ch"), Fold(Seq(Assign(Var("Odd", "ch"), Var("Odd", "ch"))))),
          "Even" -> LocalStep(Public("ch"), Fold(Seq(Assign(Var("Even", "ch"), Var("Even", "ch")))))
        ),
        timeout = 1,
        commands = Seq[Stmt]()
      ),
      BigStep(
        action = Map(
          "Odd" -> reveal("Odd", "c", "ch"),
          "Even" -> reveal("Even", "c", "ch")
        ),
        timeout = 1,
        commands = Seq[Stmt](
          Assign(Var("Global", "Winner"), BinOp(Op.EQ, Var("Odd", "c"), Var("Even", "c")))
        )
      )
    ))

  override val cols = ProgramCols(
    Map(
      "Odd" -> (true, Seq(
        LocalStep(Public("ch"), Fold(Seq(Assign(Var("Odd", "ch"), Var("Odd", "ch"))))),
        reveal("Odd", "c", "ch")
      )),
      "Even" -> (true, Seq(
        LocalStep(Public("ch"), Fold(Seq(Assign(Var("Even", "ch"), Var("Even", "ch"))))),
        reveal("Even", "c", "ch")
      ))
    ),
    Seq(1, 1), // FIX: no join timeout
    Seq(Seq(), Seq(Assign(Var("Gloval", "Winner"), BinOp(Op.EQ, Var("Odd", "c"), Var("Even", "c")))))
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
