
import scala.collection.mutable
import Syntax._
import Op.Op
import Op1.Op1

sealed class Packet
case class JoinPacket(sender: Agent, role: RoleName) extends Packet
case class SmallStepPacket(sender: Agent, role: RoleName, value: Value) extends Packet
case class ProgressPacket() extends Packet

class Model(program: ProgramRows) {

  type Scope = mutable.Map[Var, Value]
  private def make_scope () = mutable.Map[Var, Value]()

  /// per-owner object
  private val localObjects = Map[RoleName, mutable.Map[Agent, Scope]]()

  /// externally visible role variables - one scope per role, "statically allocated"
  /// similar to static variables
  /// consists only of fold variables
  private val roleClassScope = Map[RoleName, Scope]()

  private val global: Scope = make_scope()

  private var pc = 0

  def time = 0

  def receive(packet: Packet): Unit = {
    packet match {
      case SmallStepPacket(sender, role, value) =>
        val bs = program.steps(pc)
        doSmallStep(bs.action(role), sender, role, value)
      case ProgressPacket() =>
        progress(program.steps(pc))
        pc += 1
      case JoinPacket(sender, role) =>
        require(pc == 0)
        join(program.roles(role), sender, role)
    }
  }

  def join(single: Boolean, sender: Agent, role: RoleName): Unit = {
    if (single) require(!localObjects.contains(role))
    localObjects(role)(sender) = make_scope()
  }

  def doSmallStep(step: LocalStep, sender: Agent, role: RoleName, value: Value): Unit = {
    // assume each sender must only send one message

    val local = localObjects(role)(sender)
    val v = Var(role, step.action.varname)
    require(!local.contains(v))

    require(hash(value) == local(v))
    require(eval(step.action.where, global ++ local + (v -> value)) != Bool(false))

    local(v) = value
    roleClassScope(role) += (step.fold match {
      case Some(fold) => fold.v -> eval(fold.exp, global ++ local ++ roleClassScope(role))
      case None       => v -> value // single user
    })
  }

  def progress(s: BigStep): Unit = {
    require(s.timeout <= time)
    global ++= roleClassScope.values.flatten
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
    def eval(e: Exp) = this.eval(e, ctx)
    e match {
      case x : Num => x
      case x : Bool => x
      case v : Var => ctx(v)
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
