import Syntax._

sealed abstract class Tree
case class Node(owner: String, children: Seq[Tree], infset: Int) extends Tree
case class Leaf(payoff: Map[String, Int]) extends Tree

object ExtensiveNetwork {
  def make(rows: ProgramRows): Tree = {
    val actions = rows.steps.map(bs => bs.action)

    def actionToNode(actions: List[Map[RoleName, LocalStep]], env: Map[Var, Value]): Tree = {
      actions match {
        case Nil =>
          val env1 = Eval.exec(rows.finalCommands, env)
          def getPayoff(name: String) = name -> (env1.get(Var(name, "Prize")) match { case Some(Num(n)) => n case _ => 0 })
          Leaf(rows.roles.keys.map(getPayoff).toMap)
        case action :: rest =>
          val vars = (for ((role, LocalStep(Some(Public(varname, _)), _)) <- action) yield (role, varname)).toList
          varsToNode(vars, rest, env)
      }
    }

    def varsToNode(vars: List[(RoleName, Name)], rest: List[Map[RoleName, LocalStep]], env: Map[Var, Value]): Tree = {
      vars match {
        case Nil => actionToNode(rest, env)
        case (owner, varname) :: varstail =>
          val children = valuesOfType(varname).map(v => varsToNode(varstail, rest, env + (Var(owner, varname) -> v)))
          Node(owner, children, infset=rest.size)
      }
    }

    actionToNode(actions.toList, env=Map())
  }


  def valuesOfType(name: Name): List[Value] = {
    // assume bool for now
    List(Bool(true), Bool(false))
  }

  private def product(values: List[(Var, List[Value])]): List[Map[Var, Value]] = {
    values match {
      case Nil => List(Map())
      case (vr, vals) :: tail =>
        val tails = product(tail)
        vals.flatMap(v => tails.map(_ + (vr -> v)))
    }
  }
}
