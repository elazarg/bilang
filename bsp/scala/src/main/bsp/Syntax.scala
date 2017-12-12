
object Syntax {
  type Role = String
  type Name = String
  type Agent = Int

  object Op extends Enumeration {
    type Op = Value
    val EQ, LT, ADD, SUB, MAX = Value
  }
  import Op.Op

  object Op1 extends Enumeration {
    type Op1 = Value
    val NOT, MINUS = Value
  }
  import Op1.Op1

  sealed abstract class Exp
  case class Var(role: Role, name: Name) extends Exp
  case class BinOp(op: Op, left: Exp, right: Exp) extends Exp
  case class IfThenElse(cond: Exp, left: Exp, right: Exp) extends Exp
  case class UnOp(op: Op1, e: Exp) extends Exp

  sealed abstract class Value extends Exp
  case class Num(n: Int) extends Value
  case class Bool(t: Boolean) extends Value

  sealed abstract class Action
  case class Private() extends Action
  case class Publish(where: Exp = Bool(true)) extends Action
  case class Join(single: Boolean = true) extends Action

  sealed abstract class Stmt
  case class Assign(name: Name, e: Exp) extends Stmt

  case class Fold(exp: Exp, v: Var, init: Value)

  case class LocalStep(action: Action, name: Name, fold: Option[Fold] = None)

  case class BigStep(action: Map[Role, LocalStep], timeout: Int, commands: Seq[Stmt])

  case class ProgramRows(steps: Seq[BigStep])

  case class ProgramCols(
    cols: Map[Role, Seq[LocalStep]],
    progress: Seq[Int],
    global: Seq[Option[Stmt]]
  )
}

import Syntax._

object Examples {
  val OddsEvensRows = ProgramRows(Seq(
    BigStep(
      action=Map(
        "OddPlayer"  -> LocalStep(Join(), "OddPlayer" ),
        "EvenPlayer" -> LocalStep(Join(), "EvenPlayer")
      ),
      timeout = -1,
      commands=Seq[Stmt]()
    ),
    BigStep(
      action=Map(
        "OddPlayer"  -> LocalStep(Private(), "c"),
        "EvenPlayer" -> LocalStep(Private(), "c")
      ),
      timeout=1,
      commands=Seq[Stmt]()
    ),
    BigStep(
      action=Map(
        "OddPlayer"  -> LocalStep(Publish(), "c"),
        "EvenPlayer" -> LocalStep(Publish(), "c")
      ),
      timeout=1,
      commands=Seq[Stmt](
        Assign("Winner", BinOp(Op.EQ, Var("OddPlayer", "c"), Var("EvenPlayer", "c")))
      )
    )
  ))

  val OddsEvensCols = ProgramCols(
    Map(
      "OddPlayer" -> Seq(LocalStep(Join(), "OddPlayer" ), LocalStep(Private(), "c"), LocalStep(Publish(), "c")),
      "EvenPlayer"-> Seq(LocalStep(Join(), "EvenPlayer"), LocalStep(Private(), "c"), LocalStep(Publish(), "c"))
    ),
    Seq(1, 1, 1),
    Seq(None, None, Some(Assign("Winner", BinOp(Op.EQ, Var("OddPlayer", "c"), Var("EvenPlayer", "c")))))
  )
}
