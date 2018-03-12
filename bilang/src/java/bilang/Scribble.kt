package bilang

sealed class Sast {

    data class Protocol(val roles: Set<Role>, val block: Block) : Sast()

    data class Block(val stmts: List<Action>): Sast()

    sealed class Action : Sast() {
        data class Send(val label: String, val params: List<VarDec>, val from: Role, val to: Set<Role>): Action()
        data class Connect(val to: Role): Action()
        data class Choice(val at: Role, val choices: List<Block>): Action()
        data class Rec(val label: String, val actions: Block): Action()
        data class Continue(val label: String): Action()
    }

    data class Var(val name: String)
    data class Type(val name: String)
    data class Role(val name: String)
    data class VarDec(val name: String, val type: Type)

    fun prettyPrint(role: String? = null, indent: Int = 0): String {
        fun pretty(x: Sast) = x.prettyPrint(role, indent)
        val code = when (this) {
            is Sast.Protocol -> {
                assert(indent == 0)
                val ps = ", " + roles.joinToString(", ") { "role ${it.name}" }
                val scope = if (role == null) "global" else "local"
                "explicit $scope protocol MyProtocol_$role(role Server$ps) " + pretty(block)
            }
            is Block -> stmts
                    .map { it.prettyPrint(role, indent + 1) }
                    .filter{ it.isNotBlank() }
                    .joinToString(";\n", "{\n", ";\n${"    ".repeat(indent)}}\n")
            is Action.Send -> {
                val args = params.joinToString(", ") { it.type.name }
                val names = params.joinToString("_") { it.name }
                var res = "${label}_$names($args)"
                if (role == null || to.contains(Role(role)))
                    res += " from ${from.name}"
                if (role == null || from.name == role)
                    res += " to ${to.joinToString(", ") { it.name }}"
                res
            }
            is Action.Connect ->
                when (role) {
                    null -> "connect Server to ${to.name}"
                    to.name -> "connect Server"
                    else -> ""
                }
            is Action.Choice -> {
                val blocks = choices.joinToString(" or ") { pretty(it) }
                "choice at $at $blocks"
            }
            is Action.Rec -> "rec " + pretty(actions)
            is Action.Continue -> "continue $label"
        }
        return "    ".repeat(indent) + code
    }
}

object XXX {
    fun programToScribble(p: Program): Sast.Protocol {
        val roles = findRoles(p.block)
        val hides = matchRevealToHide(p.block)
        return Sast.Protocol(
            roles,
            Sast.Block(stmtToScribble(p.block, roles, hides))
        )
    }
    private val server = Sast.Role("Server")

    private fun stmtToScribble(stmt: Stmt, roles: Set<Sast.Role>, hides: Map<Stmt.Reveal, Packet>): List<Sast.Action> = when (stmt) {
        is Stmt.Def.JoinDef -> listOf(Sast.Action.Connect(makeRole(stmt.packets[0].role)))
        is Stmt.Def.YieldDef -> {
            val packets = stmt.packets
            val rec = if (packets.size > 1 || stmt.hidden) {
                packets.map { p ->
                    Sast.Action.Send("Hidden", decls(p), makeRole(p.role), setOf(server))
                }
            } else listOf()
            val pub = packets.map { p ->
                Sast.Action.Send("Public", decls(p), makeRole(p.role), setOf(server))
            }
            val bcast = packets.map { p ->
                Sast.Action.Send("Broadcast", decls(p), server, roles - makeRole(p.role))
            }
            if (stmt.hidden) rec else rec + pub + bcast
        }
        is Stmt.Reveal -> {
            val p = hides.getValue(stmt)
            listOf(Sast.Action.Send("Public", decls(p), makeRole(p.role), setOf(server)),
                    Sast.Action.Send("Reveal", decls(p), server, roles - makeRole(p.role)))
        }
        is Stmt.If -> {
            val ifTrue = stmtToScribble(stmt.ifTrue, roles, hides)
            val ifFalse = stmtToScribble(stmt.ifFalse, roles, hides)
            assert(ifTrue == ifFalse)
            ifTrue
        }
        is Stmt.Block -> stmt.stmts.flatMap { s -> stmtToScribble(s, roles, hides) }
        else -> {
            listOf()
        }
    }

    private fun decls(p: Packet): List<Sast.VarDec> {
        return p.params.map { param ->
            Sast.VarDec(param.name.name, Sast.Type((param.type as TypeExp.TypeId).name))
        }
    }

    private fun findRoles(block: Stmt.Block): Set<Sast.Role> {
        val res : MutableSet<Sast.Role> = mutableSetOf()
        for (stmt in block.stmts) when (stmt) {
            is Stmt.Def.JoinDef -> res += stmt.packets.map{ makeRole(it.role) }
            is Stmt.ForYield -> res += findRoles(stmt.block)
            is Stmt.If -> res += findRoles(stmt.ifTrue) + findRoles(stmt.ifFalse)
            else -> {}
        }
        return res.toSet()
    }

    private fun makeRole(role: Exp.Var) = Sast.Role(role.name)

    private fun matchRevealToHide(block: Stmt.Block, yields: MutableMap<String, Packet> = mutableMapOf()) : Map<Stmt.Reveal, Packet> {
        // FIX: ad-hoc - does not respect scope, flow, etc.
        val hides: MutableMap<Stmt.Reveal, Packet> = mutableMapOf()
        for (stmt in block.stmts) when (stmt) {
            is Stmt.Def.YieldDef ->
                if (stmt.hidden)
                    for (v in stmt.packets)
                        for (p in v.params)
                            yields[p.name.name] = v
            is Stmt.Reveal ->
                    hides[stmt] = yields.getValue(stmt.target.name)
            is Stmt.If -> {
                hides.putAll(matchRevealToHide(stmt.ifTrue, yields))
                hides.putAll(matchRevealToHide(stmt.ifFalse, yields))
            }
            else -> { }
        }
        return hides.toMap()
    }
}