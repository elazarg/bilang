
import scala.collection.mutable
import Syntax._
import Op.Op
import Op1.Op1


object Model {
  type Scope = mutable.Map[Var, Value]
  private val local_objects = Map[(Agent, Role), Scope]()
  private val global: Scope = mutable.Map[Var, Value]()
  private val next_global: Scope = mutable.Map[Var, Value]()

  private val assigned = mutable.Map[Agent, Var]()
  private val owner = mutable.Map[Role, Agent]()

  def time = 0

  def join(sender: Agent, role: Role, single: Boolean): Unit ={
    if (single) require(!owner.contains(role))
    owner.put(role, sender)
  }

  def receive(step: LocalStep, sender: Agent, role: Role, value: Value): Unit = {
    // assume each sender must only send one message

    // Local scope is inaccessible to others
    val local = local_objects( (sender, role) )
    val v = Var(role, step.action.name)
    require(!assigned.get(sender).contains(v))

    val scope = global ++ local
    require(hash(value) == local(v) && eval(step.action.where, scope + (v -> value)) != Bool(false))

    local.put(v, value)

    next_global += (step.fold match {
      case Some(fold) => fold.v -> eval(fold.exp, scope)
      case None       => v -> value
    })

    assigned.put(sender, v)
  }

  def progress(s: BigStep): Unit = {
    global ++= next_global
    next_global.clear()

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
      case Hash(x) => hash(eval(x))
      case UnOp(op, arg) => sem(op)(eval(arg))
      case BinOp(op, left, right) => sem(op)(eval(left), eval(right))
      case IfThenElse(cond, left, right) =>
        val Bool(b) = eval(cond)
        if (b) eval(left) else eval(right)
    }
  }

  def hash(value: Value): Num = Num(value.hashCode)

}
