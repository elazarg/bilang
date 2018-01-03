
object Syntax {
  type RoleName = String
  type Name = String
  type Agent = Int

  object Op extends Enumeration {
    type Op = Value
    val EQ, LT, ADD, SUB, MUL, DIV, MAX = Value
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
  case class Tuple(vs: Value*) extends Value

  case class Public(varname: Name, where: Exp = Bool(true))

/* Sugar:
  sealed abstract case class Action(name: Name)
  case class Private(override val name: Name) extends Action(name)
  case class Publish(override val name: Name, where: Exp = Bool(true)) extends Action(name)
*/
  sealed abstract class Stmt
  case class Assign(name: Var, e: Exp) extends Stmt

  case class Fold(inits: Seq[Stmt], stmts: Seq[Stmt])

  case class LocalStep(action: Public, fold: Fold = Fold(Seq(), Seq()))

  case class BigStep(action: Map[RoleName, LocalStep], timeout: Int, commands: Seq[Stmt])

  case class ProgramRows(roles: Map[RoleName, Boolean], steps: Seq[BigStep])

  case class ProgramCols(
    cols: Map[RoleName, (Boolean, Seq[LocalStep])],
    progress: Seq[Int],
    global: Seq[Seq[Stmt]]
  )

  def transpose(p: ProgramCols) : ProgramRows = {
    val indices = p.cols.values.head._2.indices
    ProgramRows(
      roles = p.cols.map { case (role, (single, _)) => role -> single },
      steps = indices.map { i =>
        BigStep(
          action = p.cols.map { case (role, (_, steps)) => role -> steps(i) },
          timeout = p.progress(i),
          commands = p.global(i)
        )
      }
    )
  }

  def transpose(p: ProgramRows) = ProgramCols(
    cols = p.roles.map { case (role, single) => role -> (single, p.steps.map(_.action(role))) },
    progress = p.steps.map(_.timeout),
    global = p.steps.map(_.commands)
  )

}
