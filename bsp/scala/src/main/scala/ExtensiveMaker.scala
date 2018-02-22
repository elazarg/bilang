import Syntax._

sealed abstract class Tree
case class Node(owner: String, infset: Int, children: List[(Value, Tree)]) extends Tree
case class Leaf(payoff: Map[String, Int]) extends Tree

object ExtensiveNetwork {
  def make(rows: ProgramRows): List[String] = {
    val roles = rows.roles.keys

    def actionToNode(actions: List[Map[RoleName, LocalStep]],
                     env: Map[Var, Value], subjEnv: Map[RoleName, Map[Var, Value]]): Tree = {
      actions match {
        case Nil =>
          val env1 = Eval.exec(rows.finalCommands, env)
          def getPayoff(name: String) = name -> (env1.get(Var(name, "Prize")) match { case Some(Num(n)) => n case _ => 0 })
          Leaf(roles.map(getPayoff).toMap)
        case action :: rest =>
          // TODO: Validate statically that in publish phase there's nothing other than publishing
          varsToNode(action.toList, rest, env, subjEnv)
      }
    }

    def varsToNode(vars: List[(RoleName, LocalStep)], rest: List[Map[RoleName, LocalStep]],
                   env: Map[Var, Value], subjEnv: Map[RoleName, Map[Var, Value]]): Tree = {
      vars match {
        case Nil => actionToNode(rest, env, subjEnv)
        case (_, LocalStep(None, _)) :: varstail =>
          varsToNode(varstail, rest, env, subjEnv)
        case (role, LocalStep(Some(a), _)) :: varstail =>
          val newVar = Var(role, a.varname)
          if (a.public && env.contains(newVar)) {
            val subjEnv1 = subjEnv.map{ case (r, ss) => r -> (ss + (newVar -> env(newVar)))}
            varsToNode(varstail, rest, env, subjEnv1)
          } else {
            def abs(r: RoleName, v: Value) = if (a.public || r == role) { v } else { hide(v) }
            def subjEnv1(v: Value) = subjEnv.map{ case (r, ss) => r -> (ss + (newVar -> abs(r, v))) }
            val filteredValues =
              if (env.exists{ case (vr, vl) => vr.role == role && vl == ImOut()}) List(ImOut())
              else valuesOfType(a.varname)

            val children =
              for {
                v <- filteredValues
                env1 = env + (Var(role, a.varname) -> v)
                if Eval.eval(a.where, env1) == Bool(true) || v == ImOut()
              } yield v -> varsToNode(varstail, rest, env1, subjEnv1(v))
            // todo: force ImOut if quit at any time
            // assume independence:
            Node(role, subjEnv(role).hashCode, children)
          }
      }
    }

    val subjEnv = (for (r <- roles) yield r->Map[Var, Value]()).toMap
    val tree = actionToNode(rows.steps.map(bs => bs.action).toList, env=Map(), subjEnv = subjEnv)
    val players = stringList(roles)
    List(
      s"EFG 2 R ${q(rows.name)} $players",
      q(rows.description),
      ""
    ) ++ toEfg(tree, roles.toList)
  }

  def hide(v: Value): Value = {
    v match {
      case Bool(_) => Hidden()
      case ImOut() => ImOut()
      case x => throw new Exception("" + x)
    }
  }

  var outcomeNumber = 1
  def toEfg(t: Tree, roleOrder: List[String]): List[String] = {
    t match {
      case node: Node =>
        val (values, children) = node.children.unzip
        val nodeName: String = ""
        val owner: Int = roleOrder.indexOf(node.owner)+1
        val infset: Int = node.infset+1
        val infsetName: String = ""
        val actionNamesForInfSet: String = stringList(values.map(valueToName))
        val outcome: Int = 0
        val nameOfOutcome: String = ""
        val payoffs: Int = 0
        List(s"p ${q(nodeName)} $owner $infset ${q(infsetName)} $actionNamesForInfSet $payoffs") ++ children.flatMap(toEfg(_, roleOrder))
      case leaf: Leaf =>
        val name: String = ""
        val outcome: Int = outcomeNumber // TODO: what is this exactly? must it be sequential?
        // Seems like outcomes are "named payoffs" and should define the payoff uniquely
        outcomeNumber += 1
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
