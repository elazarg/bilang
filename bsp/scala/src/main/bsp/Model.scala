import scala.collection.mutable

object Syntax {
  type Role = String
  type Name = String
  type Agent = Int

  sealed abstract class Exp
  case class Var(role: Role, name: Name) extends Exp
  case class BinOp(op: (Value, Value) => Value, left: Exp, right: Exp) extends Exp
  case class UnOp(op: Value => Value, e: Exp) extends Exp

  sealed abstract class Value extends Exp
  case class Num(n: Int) extends Value
  case class Bool(t: Boolean) extends Value

  sealed abstract class Action
  case class Private() extends Action
  case class Publish(w: Exp) extends Action
  case class Join(single: Boolean) extends Action

  sealed abstract class Stmt
  case class Assign(name: Name, e: Exp) extends Stmt

  case class Fold(exp: Exp, v: Name, init: Value)

  case class LocalStep(action: Action, name: Name)

  case class BigStep(action: Map[Role, (LocalStep, Option[Fold])], timeout: Int, commands: Seq[Stmt])

  case class Program(steps: Seq[BigStep])
}

import Syntax._

object Model {
  type Scope = mutable.Map[Var, Value]
  private val Γ = Map[Agent, Scope]()
  private val global: Scope = mutable.Map[Var, Value]()

  private val requests = mutable.Map[Agent, Var]()
  private val owner = mutable.Map[Role, Agent]()

  def time = 0

  def require(condition: Boolean): Unit = { }

  def eval(e: Exp, ctx: Scope): Value = {
    e match {
      case x @ Num(_) => x
      case x @ Bool(_) => x
      case v @ Var(_, _) => ctx(v)
      case UnOp(op, arg) => op(eval(arg, ctx))
      case BinOp(op, left, right) => op(eval(left, ctx), eval(right, ctx))
    }
  }

  def hash(value: Value): Num = Num(value.hashCode)

  def pre_step(s: BigStep): Unit = {
    for ( (k, (step, Some(fold))) <- s.action)
      global += (Var("Global", step.name) -> eval(fold.init, global))
  }

  def receive_request(s: BigStep, sender: Agent, role: Role, value: Value): Unit = {
    // assume each sender must only send one message
    val (LocalStep(action, name), maybeFold) = s.action(role)
    val v = Var(role, name)
    val local = Γ(sender)
    require(!requests.get(sender).contains(v))
    action match {
      case Join(single) =>
        if (single) require(!owner.contains(role))
        owner.put(role, sender)
      case Private() =>
        require(owner.get(role).contains(sender))
      case Publish(where) =>
        require(owner.get(role).contains(sender))
        require(hash(value) == local(v))
        require(eval(where, global ++ local + (v -> value)) != Bool(false))
        for (fold <- maybeFold) {
          global += (Var("Global", fold.v) -> eval(fold.exp, global ++ local))
        }
    }
    requests.put(sender, v)
  }

  def progress(s: BigStep): Unit = {
    val vars = (s.action map { case (role, (LocalStep(_, v), fold)) => Var(role, v) }).toSet
    val assigned = requests.values.toSet // TODO: perhaps testing fold result is better
    assert(assigned.subsetOf(vars))
    require(s.timeout <= time || vars == assigned)

    requests.clear()
    for (Assign(name, exp) <- s.commands) {
      global += Var("Global", name) -> eval(exp, global)
      // fire event here
    }
  }
}
