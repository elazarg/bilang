import Syntax._

object SNPG extends Example {
  def reveal(role: Name, v: Name, c: Name): Public = {
    Public(v, where = BinOp(Op.EQ, Hash(Var(role, v)), Var(role, c)))
  }

  private val fold = Fold(
    inits = Seq(
      Assign(Var("Player", "S"), Num(0)),
      Assign(Var("Player", "Count"), Num(0))
    ),
    stmts = Seq(
      Assign(Var("Player", "S"), BinOp(Op.ADD, Var("Player", "S"), Var("Player", "bet"))),
      Assign(Var("Player", "Count"), BinOp(Op.ADD, Var("Player", "Count"), Num(1)))
    )
  )
  private val payment = Assign(Var("Global", "Payment"), BinOp(Op.DIV, Var("Player", "S"), Var("Player", "Count")))

  override val rows = ProgramRows(
    Map("Player" -> false),
    Seq(
      BigStep(
        action = Map("Player"  -> LocalStep(Public("beth"))),
        timeout = 1,
        commands = Seq()
      ),
      BigStep(
        action = Map("Player" -> LocalStep(reveal("Player", "bet", "beth"), fold)),
        timeout = 1,
        commands = Seq(payment)
      )
    )
  )

  override val cols = ProgramCols(
    Map("Player" -> (false, Seq(LocalStep(Public("beth")), LocalStep(reveal("Player", "bet", "beth"), fold)))),
    Seq(1, 1), // FIX: no join timeout
    Seq(Seq(), Seq(payment))
  )

  def player(n: Int): Strategy = {
    case List() => JoinPacket(this, -1, "Player")
    case List(_) => SmallStepPacket(this, 0, "Player", Utils.hash(Num(n)))
    case List(_, _) => SmallStepPacket(this, 1, "Player", Num(n))
    case List(_, _, _) => DisconnectPacket(this, 2, "Player")
  }

  val players = List(player(50), player(150))
}
