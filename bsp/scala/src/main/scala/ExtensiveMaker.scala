import Syntax._

sealed abstract class Tree
case class Node(owner: String, infset: Int, children: Map[Value, Tree]) extends Tree
case class Leaf(payoff: Map[String, Int]) extends Tree

object ExtensiveNetwork {
  def make(rows: ProgramRows): List[String] = {
    val actions = rows.steps.map(bs => bs.action)
    val roles = rows.roles.keys

    def actionToNode(actions: List[Map[RoleName, LocalStep]], env: Map[Var, Value]): Tree = {
      actions match {
        case Nil =>
          val env1 = Eval.exec(rows.finalCommands, env)
          def getPayoff(name: String) = name -> (env1.get(Var(name, "Prize")) match { case Some(Num(n)) => n case _ => 0 })
          Leaf(roles.map(getPayoff).toMap)
        case action :: rest =>
          val vars = (for ((role, LocalStep(Some(Public(varname, where)), _)) <- action) yield (role, varname, where)).toList
          varsToNode(vars, rest, env)
      }
    }

    def varsToNode(vars: List[(RoleName, Name, Exp)], rest: List[Map[RoleName, LocalStep]], env: Map[Var, Value]): Tree = {
      vars match {
        case Nil => actionToNode(rest, env)
        case (owner, varname, where) :: varstail =>
          val children = valuesOfType(varname)
            .filter(v => Eval.eval(where, env + (Var(owner, varname) -> v)) == Bool(true))
            .map(v => v -> varsToNode(varstail, rest, env + (Var(owner, varname) -> v)))
          // assume independence:
          Node(owner, rest.size, children.toMap)
      }
    }

    val tree = actionToNode(actions.toList, env=Map())
    val players = stringList(roles)
    List(
      s"EFG 2 R ${q(rows.name)} $players",
      q(rows.description),
      ""
    ) ++ toEfg(tree, roles.toList)
  }

  var n = 1
  def toEfg(t: Tree, roleOrder: List[String]): List[String] = {
    t match {
      case node: Node =>
        val nodeName: String = ""
        val owner: Int = roleOrder.indexOf(node.owner)+1
        val infset: Int = node.infset+1
        val infsetName: String = ""
        val actionNamesForInfSet: String = stringList(node.children.keys.map(valueToName))
        val outcome: Int = 0
        val nameOfOutcome: String = ""
        val payoffs: Int = 0
        val children = valuesOfType("").map(node.children.apply)
        List(s"p ${q(nodeName)} $owner $infset ${q(infsetName)} $actionNamesForInfSet $payoffs") ++ children.flatMap(toEfg(_, roleOrder))
      case leaf: Leaf =>
        val name: String = ""
        val outcome: Int = n // TODO: what is this exactly? must it be sequential?
        // Seems like outcomes are "named payoffs" and should define the payoff uniquely
        n += 1
        val nameOfOutcome: String = ""
        val payoffs = roleOrder.map(leaf.payoff(_)).mkString("{ ", ", ", " }")
        List(s"t ${q(name)} $outcome ${q(nameOfOutcome)} $payoffs")
    }
  }
  def q(name: String) = '"' + name + '"'
  def stringList(ss: Iterable[String]) = ss.map(q).mkString("{ ", " ", " }")

  def valueToName(v: Value): String = {
    v match {
      case Bool(b) => b.toString
      case Num(n) => n.toString
      case ImOut() => "None"
      case x => throw new Exception(x.toString)
    }
  }

  def valuesOfType(name: Name): List[Value] = {
    // assume bool for now
    List(Bool(true), Bool(false), ImOut())
  }

}
