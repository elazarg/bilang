
import scala.collection.mutable
import Syntax._
import Op.Op
import Op1.Op1

sealed abstract class Packet
case class JoinPacket(sender: Agent, role: RoleName) extends Packet
case class SmallStepPacket(sender: Agent, role: RoleName, value: Value) extends Packet
case class ProgressPacket() extends Packet

object Utils {
  def hash(value: Value): Num = Num(value.hashCode)
}

class Model(program: ProgramRows) {

  private var pc = -1

  def receive(packet: Packet): Unit = packet match {
    case SmallStepPacket(sender, role, value) =>
      doSmallStep(program.steps(pc).action(role), sender, role, value)
    case ProgressPacket() =>
      if (pc >= 0)
        progress(program.steps(pc))
      pc += 1
    case JoinPacket(sender, role) =>
      require(pc == -1)
      join(program.roles(role), sender, role)
  }

  private type Scope = mutable.Map[Var, Value]
  private def makeScope () = mutable.Map[Var, Value]()

  /// per-owner object
  private val localObjects =
    program.roles.keys.map(_ -> mutable.Map[Agent, Scope]()).toMap

  /// externally visible role variables - one scope per role, "statically allocated"
  /// similar to static variables
  /// consists only of fold variables
  private val roleClassScope: Map[RoleName, Scope] =
    program.roles.keys.map(_ -> makeScope()).toMap

  private val global: Scope = makeScope()

  private def time = 100

  private def join(single: Boolean, sender: Agent, role: RoleName): Unit = {
    if (single) require(localObjects(role).isEmpty)
    localObjects(role)(sender) = makeScope()
  }

  private def doSmallStep(step: LocalStep, sender: Agent, role: RoleName, value: Value): Unit = {
    // assume each sender must only send one message

    val scope = roleClassScope(role)
    val local = localObjects(role)(sender)
    val v = Var(role, step.action.varname)
    require(!local.contains(v))

    require(eval(step.action.where, global ++ local + (v -> value)) != Bool(false))

    local(v) = value

    global ++= exec(step.fold.stmts, global ++ local)
  }

  private def progress(s: BigStep): Unit = {
    require(s.timeout <= time)
    global ++= roleClassScope.values.flatten
    global ++= exec(s.commands, global)
  }

  private def require(condition: Boolean): Unit = {
    if (!condition)
      throw new Exception()
  }
  def exec(block: Iterable[Stmt], scope: Scope): Scope = {
    val local = makeScope()
    for (Assign(v, exp) <- block)
      local += v -> eval(exp, scope ++ local)
    local
  }

  private def applyOp(op: Op1, e: Value) : Value = {
    (op, e) match {
      case (Op1.NOT, Bool(x)) =>  Bool(!x)
      case (Op1.MINUS, Num(x)) => Num(-x)
      case _ => ???
    }
  }

  private def applyOp(op: Op, left: Value, right: Value) : Value = {
    (op, left, right) match {
      case (Op.EQ, _, _) =>  Bool(left == right)
      case (Op.LT, Num(x), Num(y)) => Bool(x < y)
      case (Op.ADD, Num(x), Num(y)) => Num(x + y)
      case (Op.SUB, Num(x), Num(y)) => Num(x - y)
      case (Op.MAX, Num(x), Num(y)) => Num(Math.max(x, y))
      case _ => ???
    }
  }

  private def eval(e: Exp, ctx: Scope): Value = {
    def eval(e: Exp) = this.eval(e, ctx)
    e match {
      case x : Value => x
      case v : Var => ctx(v)
      case Hash(x) => Utils.hash(eval(x))
      case UnOp(op, arg) => applyOp(op, eval(arg))
      case BinOp(op, left, right) => applyOp(op, eval(left), eval(right))
      case IfThenElse(cond, left, right) =>
        val Bool(b) = eval(cond)
        if (b) eval(left) else eval(right)
    }
  }

}

class Network(contract: Model) {
  def run(packets: Seq[Packet]): Unit = {
    for (p <- packets)
      contract.receive(p)
  }
}
