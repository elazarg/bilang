
// TODO: STATIC BINDING! yes, as an implementation detail. But static. binding.


object Syntax {
  type RoleName = String
  type Name = String
  type Agent = Any

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
  case class ImOut() extends Value
  case class Num(n: Int) extends Value
  case class Bool(t: Boolean) extends Value
  case class Tuple(vs: Value*) extends Value

  case class Public(varname: Name, where: Exp = Bool(true))

  sealed abstract class Stmt
  case class Assign(name: Var, e: Exp) extends Stmt

  case class Fold(inits: Seq[Stmt], stmts: Seq[Stmt])

  case class LocalStep(action: Option[Public], fold: Fold = Fold(Seq(), Seq()))

  case class BigStep(action: Map[RoleName, LocalStep], timeout: Int)

  case class ProgramRows(roles: Map[RoleName, Boolean], steps: Seq[BigStep], finalCommands: Seq[Stmt] = Seq(),
                         name: String = "", description: String = "")

  case class ProgramCols(
    cols: Map[RoleName, (Boolean, Seq[LocalStep])],
    progress: Seq[Int],
    finalCommands: Seq[Stmt] = Seq(),
    name: String = "",
    description: String = ""
  )

  def transpose(p: ProgramCols) : ProgramRows = {
    val indices = p.cols.values.head._2.indices
    ProgramRows(
      roles = p.cols.map { case (role, (single, _)) => role -> single },
      steps = indices.map { i =>
        BigStep(
          action = p.cols.map { case (role, (_, steps)) => role -> steps(i) },
          timeout = p.progress(i)
        )
      },
      finalCommands = p.finalCommands
    )
  }

  def transpose(p: ProgramRows) = ProgramCols(
    cols = p.roles.map { case (role, single) => role -> (single, p.steps.map(_.action(role))) },
    progress = p.steps.map(_.timeout),
    finalCommands = p.finalCommands
  )

  def validate(rows: ProgramRows): Boolean = {
    val defined = collection.mutable.Set[Name]()
    val roles = rows.roles.keys.toSet
    for (bigstep <- rows.steps) {
      if (bigstep.action.keySet != roles)
        return false
      for ( (role, LocalStep(Some(Public(varname, where)), Fold(inits, stmts)) ) <- bigstep.action ){
        defined += varname

        if (! freeVars(where).subsetOf(defined)) return false

        for (Assign(Var(_, name), e) <- inits) {
          if (! freeVars(e).subsetOf(defined)) return false
          defined += name
        }
        // stmts can only use names, not declare names. TODO: add Declare() statement
        for (Assign(Var(_, name), e) <- stmts) {
          if (! freeVars(e).subsetOf(defined)) return false
          if (! defined.contains(name)) return false
        }
      }
    }
    true
  }


  private def freeVars(exp: Exp): Set[Name] = exp match {
    case _ : Value => Set()
    case Var(_, name) => Set(name)
    case Hash(e) => freeVars(e)
    case UnOp(_, arg) => freeVars(arg)
    case BinOp(_, left, right) => freeVars(left) ++ freeVars(right)
    case IfThenElse(cond, left, right) => freeVars(cond) ++ freeVars(left) ++ freeVars(right)
  }
}
