
import scala.collection.mutable
import Syntax._
import Op.Op
import Op1.Op1


object Model {
  type Scope = mutable.Map[Var, Value]
  private val Γ = Map[Agent, Scope]()
  private val global: Scope = mutable.Map[Var, Value]()

  private val assigned = mutable.Map[Agent, Var]()
  private val owner = mutable.Map[Role, Agent]()

  def time = 0

  def receive_request(step: LocalStep, sender: Agent, role: Role, value: Value): Unit = {
    // assume each sender must only send one message
    val local = Γ(sender)

    def noReenter(name: Name) (conditions: Var => Boolean) = {
      val v = Var(role, name)
      require(!assigned.get(sender).contains(v))
      if (owner.get(role).contains(sender) && conditions(v))
        assigned.put(sender, v)
    }

    step.action match {
      case Join(single) =>
        if (single) require(!owner.contains(role))
        owner.put(role, sender)

      case Private(name) =>
        noReenter(name) { _ => true }

      case Publish(name, where) =>
        noReenter(name) { v =>
          hash(value) == local(v) &&
          eval(where, global ++ local + (v -> value)) != Bool(false)
        }
        // FIX: update local?
    }
    // Fix: Fold is required; when not specified (for singleton roles),
    // it is a simple assignment from local to global.
    for (fold <- step.fold)
      global += fold.v -> eval(fold.exp, global ++ local)
  }

  def progress(s: BigStep): Unit = {
    val declared_vars = (s.action map { case (role, LocalStep(action, _)) => Var(role, action.name) }).toSet
    val assigned_vars = assigned.values.toSet // TODO: perhaps testing fold result is better
    assert(assigned_vars.subsetOf(declared_vars))
    require(s.timeout <= time || declared_vars == assigned_vars)

    assigned.clear()
    for (Assign(name, exp) <- s.commands) {
      global += Var("Global", name) -> eval(exp, global)
      // fire event here
    }
  }

  def pre_step(s: BigStep): Unit = {
    // FIX: Should happen at the global phase of previous step, to avoid the loop
    for ( (_, LocalStep(_, Some(fold))) <- s.action)
      global += (fold.v -> eval(fold.init, global))
  }

  def require(condition: Boolean): Unit = { }

  def sem(op: Op1) (e: Value) : Value = {
    (op, e) match {
      case (Op1.NOT, Bool(x)) =>  Bool(!x)
      case (Op1.MINUS, Num(x)) => Num(-x)
      case _ => ???
    }
  }

  def sem(op: Op) (left: Value, right: Value) : Value = {
    (op, left, right) match {
      case (Op.EQ, _, _) =>  Bool(left == right)
      case (Op.LT, Num(x), Num(y)) => Bool(x < y)
      case (Op.ADD, Num(x), Num(y)) => Num(x + y)
      case (Op.SUB, Num(x), Num(y)) => Num(x - y)
      case (Op.MAX, Num(x), Num(y)) => Num(Math.max(x, y))
      case _ => ???
    }
  }

  def eval(e: Exp, ctx: Scope): Value = {
    def eval(e: Exp) = Model.eval(e, ctx)
    e match {
      case x @ Num(_) => x
      case x @ Bool(_) => x
      case v @ Var(_, _) => ctx(v)
      case UnOp(op, arg) => sem(op)(eval(arg))
      case BinOp(op, left, right) => sem(op)(eval(left), eval(right))
      case IfThenElse(cond, left, right) =>
        val Bool(b) = eval(cond)
        if (b) eval(left) else eval(right)
    }
  }

  def hash(value: Value): Num = Num(value.hashCode)

}
