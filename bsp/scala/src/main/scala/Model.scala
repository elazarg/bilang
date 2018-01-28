
import scala.collection.mutable
import Syntax._
import Op.Op
import Op1.Op1

sealed abstract class Packet
case class JoinPacket(sender: Agent, pc: Int, role: RoleName) extends Packet
case class SmallStepPacket(sender: Agent, pc: Int, role: RoleName, value: Value) extends Packet
case class ProgressPacket(pc: Int) extends Packet
case class DisconnectPacket(sender: Agent, pc: Int, role: RoleName) extends Packet


object Model {
  type Event = StepState
}

case class StepState (
  val static: Map[Var, Value],
  val objects: Map[Agent, Map[Var, Value]]
)

class PendingStepState {
  val static = mutable.Map[Var, Value]()
  val objects = mutable.Map[Agent, mutable.Map[Var, Value]]()

  def freezeAndClear(): StepState = {
    val res = StepState(
      static=static.toMap,
      objects=objects.map{ case (k, v) => k -> v.toMap }.toMap
    )
    static.clear()
    objects.values.foreach(_.clear())
    res
  }
}

class Model(program: ProgramRows) {
  var state: List[StepState] = List()

  private val pendingState = new PendingStepState()

  def pc: Int = state.size - 1

  def receive(packet: Packet, time: Int): Unit = packet match {
    case JoinPacket(sender, _pc, role) =>
      require(_pc == -1)
      require(_pc == pc)
      join(program.roles(role), sender, role)

    case SmallStepPacket(sender, _pc, role, value) =>
      require(_pc == pc)
      doSmallStep(program.steps(pc).action(role), sender, role, value)

    case ProgressPacket(_pc) =>
      require(_pc == pc)
      if (pc >= 0) {
        require(time - steptime >= program.steps(pc).timeout)
        steptime = time
      }
      state :+= pendingState.freezeAndClear()
      if (program.steps.lengthCompare(pc) > 0) { // pc < steps.size
        for ((_, step) <- program.steps(pc).action)
          execFold(step.fold.inits)
      } else {
        Eval.exec(program.finalCommands, lookup(_, None))
      }

    case DisconnectPacket(_, _pc, _) =>
      require(_pc == pc)
  }

  var steptime = 0

  private def join(single: Boolean, sender: Agent, role: RoleName): Unit = {
    if (single) require(pendingState.objects.get(sender).isEmpty)
    pendingState.objects(sender) = mutable.Map[Var, Value]()
  }

  private def lookup(v: Var, maybeAgent: Option[Agent] = None): Value = {
    for (s <- state.reverse) {
      for (agent <- maybeAgent)
        for (res <- s.objects(agent).get(v))
          return res
      for (res <- s.static.get(v))
        return res
    }
    throw new Exception(v.toString + " not found")
  }

  private def doSmallStep(step: LocalStep, sender: Agent, role: RoleName, value: Value): Unit = {
    // assume each sender must only send one message
    if (step.action.isEmpty) return
    val action = step.action.get

    val v = Var(role, action.varname)
    require(!pendingState.objects.contains( (sender, v) ))

    def ctx(v1: Var): Value =
      if (v == v1) value else lookup(v1, Some(sender))

    require(Eval.eval(action.where, ctx) == Bool(true))

    pendingState.objects(sender)(v) = value
    execFold(step.fold.stmts, ctx)
  }

  private def execFold(stmts: Seq[Stmt], ctx: Var => Value = lookup(_, None)): Unit = {
    println(stmts)
    // Lookup on fold should consider pending state. This is not the elegant solution though
    val more = Eval.exec(stmts, v => pendingState.static.getOrElse(v, ctx(v)))
    println(" -> " + more)
    pendingState.static ++= more
  }

  private def require(condition: Boolean): Unit = {
    if (!condition)
      throw new Exception()
  }

  override def toString: String = (state, pendingState).toString
}

object Eval {

  def exec(block: Iterable[Stmt], ctx: Var => Value): Map[Var, Value] = {
    val tempScope = mutable.Map[Var, Value]()
    for (Assign(v, exp) <- block)
      tempScope += v -> eval(exp, v => tempScope.getOrElse(v, ctx(v)))
    tempScope.toMap
  }

  private def applyOp(op: Op1, e: Value) : Value = {
    (op, e) match {
      case (Op1.NOT, Bool(x)) =>  Bool(!x)
      case (Op1.MINUS, Num(x)) => Num(-x)
      case _ => ???
    }
  }

   def applyOp(op: Op, left: Value, right: Value) : Value = {
    (op, left, right) match {
      case (Op.EQ, _, _) =>  Bool(left == right)
      case (Op.LT, Num(x), Num(y)) => Bool(x < y)
      case (Op.ADD, Num(x), Num(y)) => Num(x + y)
      case (Op.SUB, Num(x), Num(y)) => Num(x - y)
      case (Op.MAX, Num(x), Num(y)) => Num(Math.max(x, y))
      case (Op.DIV, Num(_), Num(0)) => ???
      case (Op.DIV, Num(x), Num(y)) => Num(x / y)
      case _ => ???
    }
  }

   def eval(e: Exp, ctx: Var => Value): Value = {
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
