object T {
  type RoleVarname = String
  type Varname = String
  type Exp = String
  type WhereExp = String
  type FoldExp = String
}

object V {
  type Value = Int
  type Agent = Int
}

import T._
import V._

case class Var(role: RoleVarname, v: Varname, agent: Agent)

import scala.collection.mutable

sealed abstract class Action
case class Private() extends Action
case class Publish(w: WhereExp) extends Action
case class Join(single: Boolean) extends Action

case class Fold(exp: FoldExp, v: Varname, init: Value)

case class BigStep(
  action: Map[RoleVarname, (Action, Varname, Option[Fold])],
  timeout: Int,
  commands: List[(Varname, Exp)]
)

case class Program(steps: Seq[BigStep])

object Main {
  private val requests = mutable.HashMap[Var, Value]()
  private var Γ = Map[Var, Value]()

  def time = 0

  def require(condition: Boolean): Unit = { }
  def evaluate(where: WhereExp, context: Map[Var, Value]): Value = ???

  def hash(value: Value): Int = value.hashCode

  def pre_step(): Unit = {
    // initialize fold expression
  }

  def receive(s: BigStep, sender: Agent, role: RoleVarname, value: Value): Unit = {
    val (action, varname, maybeFold) = s.action(role)
    val v = Var(role, varname, sender)
    val ownerVar = Var(role, "owner", 0)
    val owner = Γ.get(ownerVar)
    action match {
      case Join(bound) =>
        if (bound) require(owner.isEmpty)
        Γ += ownerVar -> sender
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
    val assigned = requests.keySet.map {case Var(role, v, _) => (role, v)}
    assert(assigned.subsetOf(vars))
    require(s.timeout <= time || vars == assigned)
    Γ ++= requests
    requests.clear()
  }

  private def global(v: Varname) = Var("Global", v, 0)
}
