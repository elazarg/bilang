import scala.collection.mutable

object T {
  type RoleVarname = String
  type Varname = String
  type FoldExp = String
}

object V {
  type Value = Int
  type Agent = Int
}

import T._
import V._

sealed abstract class Exp
case class Name(s: String) extends Exp
case class Num(n: Int) extends Exp
case class BinOp(op: (Num, Num) => Num, left: Exp, right: Exp) extends Exp

sealed abstract class BoolExp
case class BName(s: String) extends BoolExp
case class Bool(t: Boolean) extends BoolExp
case class Not(e: BoolExp) extends BoolExp
case class CmpOp(op: (Num, Num) => Bool, left: Exp, right: Exp) extends BoolExp
case class BoolOp(op: (Bool, Bool) => Bool, left: BoolExp, right: BoolExp) extends BoolExp


sealed abstract class Action
case class Private() extends Action
case class Publish(w: BoolExp) extends Action
case class Join(single: Boolean) extends Action

case class Fold(exp: FoldExp, v: Varname, init: Value)

case class Cell(role: RoleVarname, v: Varname, agent: Agent)

case class BigStep(
  action: Map[RoleVarname, (Action, Varname, Option[Fold])],
  timeout: Int,
  commands: List[(Varname, Exp)]
)

case class Program(steps: Seq[BigStep])

object Main {
  private val requests = mutable.HashMap[Cell, Value]()
  private var Γ = Map[Cell, Value]()

  def time = 0

  def require(condition: Boolean): Unit = { }

  def eval(e: Exp)(implicit ctx: Map[Name, Num]): Num = {
    e match {
      case x @ Num(_) => x
      case v @ Name(_) => ctx(v)
      case BinOp(op, left, right) => op(eval(left), eval(right))
    }
  }

  def eval(e: BoolExp)(implicit ctx: Map[Name, Bool]): Bool = {
    e match {
      case x @ Bool(_) => x
      case v @ BName(_) => ctx(v)
      case CmpOp(op, left, right) => op(eval(left), eval(right))
      case BoolOp(op, left, right) => op(eval(left), eval(right))
    }
  }

  def evaluate(where: BoolExp, context: Map[Cell, Value]): Value = ???

  def hash(value: Value): Int = value.hashCode

  def pre_step(): Unit = {
    // initialize fold expression
  }

  def receive_request(s: BigStep, sender: Agent, role: RoleVarname, value: Value): Unit = {
    val (action, varname, maybeFold) = s.action(role)
    val v = Cell(role, varname, sender)
    val ownerCell = Cell(role, "owner", 0)
    val owner = Γ.get(ownerCell)
    action match {
      case Join(single) =>
        if (single) require(owner.isEmpty)
        Γ += ownerCell -> sender
      case Private() =>
        require(owner.contains(sender))
      case Publish(where) =>
        require(owner.get == sender)
        require(hash(value) == Γ(v))
        require(evaluate(where, Γ + (v -> value)) != 0)
        for (fold <- maybeFold) {
          require(!requests.contains(v))
          Γ += (global(fold.v) -> evaluate(fold.exp, Γ))
        }
    }
    requests.put(v, value)
  }

  def progress(s: BigStep): Unit = {
    val vars = (s.action map { case (k, (_, v, _)) => (k, v) }).toSet
    val assigned = requests.keySet.map {case Cell(role, v, _) => (role, v)}
    assert(assigned.subsetOf(vars))
    require(s.timeout <= time || vars == assigned)
    Γ ++= requests
    requests.clear()
  }

  private def global(v: Varname) = Cell("Global", v, 0)
}
