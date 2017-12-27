
object Syntax {
  type RoleName = String
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
  case class Var(role: RoleName, name: Name) extends Exp
  case class BinOp(op: Op, left: Exp, right: Exp) extends Exp
  case class IfThenElse(cond: Exp, left: Exp, right: Exp) extends Exp
  case class UnOp(op: Op1, e: Exp) extends Exp
  case class Hash(e: Exp) extends Exp

  sealed abstract class Value extends Exp
  case class Num(n: Int) extends Value
  case class Bool(t: Boolean) extends Value

  case class Public(varname: Name, where: Exp = Bool(true))

/* Sugar:
  sealed abstract case class Action(name: Name)
  case class Private(override val name: Name) extends Action(name)
  case class Publish(override val name: Name, where: Exp = Bool(true)) extends Action(name)
*/
  sealed abstract class Stmt
  case class Assign(name: Name, e: Exp) extends Stmt

  case class Fold(exp: Exp, v: Var, init: Value)

  case class LocalStep(action: Public, fold: Option[Fold] = None)

  case class BigStep(action: Map[RoleName, LocalStep], timeout: Int, commands: Seq[Stmt])

  case class ProgramRows(roles: Map[RoleName, Boolean], steps: Seq[BigStep])

  case class ProgramCols(
    cols: Map[RoleName, (Boolean, Seq[LocalStep])],
    progress: Seq[Int],
    global: Seq[Seq[Stmt]]
  )
}

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
      "Odd" -> (true, Seq(LocalStep(Public("ch")), LocalStep(reveal("Odd", "c", "ch")))),
      "Even"-> (true, Seq(LocalStep(Public("ch")), LocalStep(reveal("Even", "c", "ch"))))
    ),
    Seq(-1, -1, -1),
    Seq(Seq(), Seq(Assign("Winner", BinOp(Op.EQ, Var("Odd", "c"), Var("Even", "c")))))
  )

  def transpose(p: ProgramCols) : ProgramRows = {
    val (roles: Map[RoleName, Boolean], actions: Seq[Map[RoleName, LocalStep]]) = p.cols.map {
      case (role, (single, local_steps)) => (role -> single, local_steps.map( step => role -> step) )
    }.unzip

    val steps = (actions, p.progress, p.global).zipped.map {
      case (action, timeout, commands) => BigStep(action.toMap, timeout, commands)
    }.toSeq

    ProgramRows(roles, steps)
  }

  def transpose(p: ProgramRows) = ProgramCols(
    cols = p.roles.map { case (role, single) => role -> (single, p.steps.map(_.action(role))) },
    progress = p.steps.map(_.timeout),
    global = p.steps.map(_.commands)
  )

  def main(): Unit = {
    assert(transpose(oddsEvensCols) == oddsEvensRows)
    assert(transpose(oddsEvensRows) == oddsEvensCols)
  }
}
