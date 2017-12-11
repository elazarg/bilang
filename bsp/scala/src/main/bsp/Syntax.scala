object T {
  type RoleVarname = String
  type Varname = String
  case class Var(role: RoleVarname, v: Varname)
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

import scala.collection.mutable

sealed abstract class Action
case class Private() extends Action
case class Publish(w: WhereExp) extends Action
case class Join() extends Action
case class JoinSet() extends Action

case class Fold(exp: FoldExp, v: Varname, init: Value)

case class BigStepProg(
  action: Map[RoleVarname, (Action, Varname, Option[Fold])],
  timeout: Int,
  commands: List[(Varname, Exp)]
)

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

  def receive(s: BigStepProg, from: Agent, role: RoleVarname, value: Value): Unit = {
    val (action, varname, maybeFold) = s.action(role)
    val v = Var(role, varname)
    val owner = Γ.get(Var(role, "owner"))
    action match {
      case Join() =>    require(owner.isEmpty)
      case JoinSet() =>
        // join set - indexed by sender id?
      case Private() => require(owner.contains(from))
      case Publish(where) =>
        require(owner.contains(from))
        require(hash(value) == Γ(v))
        require(evaluate(where, Γ + (v -> value)) != 0)
        for (fold <- maybeFold) {
            require(!requests.contains(v))
          Γ += (global(fold.v) -> evaluate(fold.exp, Γ))
        }
    }
    requests.put(v, value)
  }

  def progress(s: BigStepProg): Unit = {
    val vars: Set[Var] = (s.action map { case (k, (_, v, _)) => Var(k, v) }).toSet
    val assigned = requests.keySet
    assert(assigned.subsetOf(vars))
    require(s.timeout <= time || vars == assigned)
    Γ ++= requests
    requests.clear()
  }

  private def global(v: Varname) = Var("Global", v)
}
