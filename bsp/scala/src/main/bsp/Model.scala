
import scala.collection.mutable
import Syntax._
import Op.Op
import Op1.Op1


object Model {
  type Scope = mutable.Map[Var, Value]
  private val Γ = Map[Agent, Scope]()
  private val global: Scope = mutable.Map[Var, Value]()

  private val requests = mutable.Map[Agent, Var]()
  private val owner = mutable.Map[Role, Agent]()

  def time = 0

  def receive_request(s: BigStep, sender: Agent, role: Role, value: Value): Unit = {
    // assume each sender must only send one message
    val (LocalStep(action, name), fold) = s.action(role)
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
    }
    // Fold is required; when not specified (for singleton roles),
    // it is a simple assignment from local to global.
    global += fold.get.v -> eval(fold.get.exp, global ++ local)
    requests.put(sender, v)
  }

  def progress(s: BigStep): Unit = {
    val vars = (s.action map { case (role, (LocalStep(_, v), _)) => Var(role, v) }).toSet
    val assigned = requests.values.toSet // TODO: perhaps testing fold result is better
    assert(assigned.subsetOf(vars))
    require(s.timeout <= time || vars == assigned)

    requests.clear()
    for (Assign(name, exp) <- s.commands) {
      global += Var("Global", name) -> eval(exp, global)
      // fire event here
    }
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

  def pre_step(s: BigStep): Unit = {
    // FIX: Should happen at the global phase of previous step, to avoid the loop
    for ( (_, (_, Some(fold))) <- s.action)
      global += (fold.v -> eval(fold.init, global))
  }

}
