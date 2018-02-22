import Syntax._

sealed abstract class Tree
case class Node(owner: String, infset: Int, children: Map[Value, Tree]) extends Tree
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
          val children = valuesOfType(varname).map(v => v -> varsToNode(varstail, rest, env + (Var(owner, varname) -> v)))
          // assume independence:
          Node(owner, rest.size, children.toMap)
      }
    }

    actionToNode(actions.toList, env=Map())
  }

  var n = 1
  def toEfg(t: Tree, roleOrder: List[String]): List[String] = {
    t match {
      case node: Node =>
        val nodeName: String = ""
        val owner: Int = roleOrder.indexOf(node.owner)+1
        val infset: Int = node.infset+1
        val infsetName: String = ""
        val actionNamesForInfSet: String = List(q("1"), q("2")).mkString("{ ", " ", " }")
        val outcome: Int = 0
        val nameOfOutcome: String = ""
        val payoffs: Int = 0
        val children = valuesOfType("").map(node.children(_))
        List(s"p ${q(nodeName)} $owner $infset ${q(infsetName)} $actionNamesForInfSet $payoffs") ++ children.flatMap(toEfg(_, roleOrder))
      case leaf: Leaf =>
        val name: String = ""
        val outcome: Int = n
        n += 1
        val nameOfOutcome: String = ""
        val payoffs = roleOrder.map(leaf.payoff(_)).mkString("{ ", ", ", " }")
        List(s"t ${q(name)} $outcome ${q(nameOfOutcome)} $payoffs")
    }
  }
  def q(name: String) = '"' + name + '"'
  def valuesOfType(name: Name): List[Value] = {
    // assume bool for now
    List(Bool(true), Bool(false))
  }

}
