package bilang

sealed class ScribbleAst {

    data class Protocol(val roles: Set<Role>, val block: Block) : ScribbleAst()

    data class Block(val stmts: List<Action>): ScribbleAst()

    sealed class Action : ScribbleAst() {
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

    fun prettyPrint(indent: Int): String {
        fun pretty(x: ScribbleAst) = x.prettyPrint(indent)

        val code = when (this) {
            is Action.Send -> {
                val args = params.joinToString(", ") { x -> x.type.name }
                "$label($args) from ${from.name} to ${to.joinToString(", ") { x->x.name}}"
            }
            is Action.Connect -> "connect Server to ${to.name}"
            is Action.Choice -> {
                val blocks = choices.joinToString(" or ") { x -> pretty(x) }
                "choice at $at $blocks"
            }
            is Action.Rec -> "rec " + pretty(actions)
            is Action.Continue -> "continue $label"
            is Block -> stmts.joinToString(";\n", "{\n", ";\n${"    ".repeat(indent)}}\n") { stmt -> stmt.prettyPrint(indent + 1) }
            is ScribbleAst.Protocol -> {
                assert(indent == 0)
                val ps = if (roles.isEmpty()) "" else (", " + roles.joinToString(", ") { x -> "role " + x.name })
                "explicit global protocol MyProtocol(role Server$ps) " + pretty(block)
            }
        }
        return "    ".repeat(indent) + code
    }
}

object XXX {
    fun programToScribble(p: Program): ScribbleAst.Protocol {
        val roles = findRoles(p.block)
        return ScribbleAst.Protocol(
            roles,
            ScribbleAst.Block(p.block.stmts.flatMap { stmt -> stmtToScribble(stmt, roles) })
        )
    }

    private fun stmtToScribble(stmt: Stmt, roles: Set<ScribbleAst.Role>): List<ScribbleAst.Action> = when (stmt) {
        is Stmt.Def.JoinDef -> listOf(ScribbleAst.Action.Connect(ScribbleAst.Role(stmt.packets.packets[0].role)))
        is Stmt.Def.YieldDef -> {
            val server = ScribbleAst.Role("Server")
            stmt.packets.packets.flatMap { p ->
                val params = packetToParams(p)
                listOf(
                        ScribbleAst.Action.Send("SomeLabel", params, ScribbleAst.Role(p.role), setOf(server)),
                        ScribbleAst.Action.Send("SomeLabel", params, server, roles)
                )
            }
        }
        else -> {
            listOf()
        }
    }

    private fun packetToParams(p: Packet): List<ScribbleAst.VarDec> {
        return p.params.map { param ->
            ScribbleAst.VarDec(param.name, ScribbleAst.Type((param.type as TypeExp.TypeId).name))
        }
    }

    fun findRoles(block: Block): Set<ScribbleAst.Role> {
        val res : MutableSet<ScribbleAst.Role> = mutableSetOf()
        for (stmt in block.stmts) when (stmt) {
            is Stmt.Def.JoinDef -> res += stmt.packets.packets.map{ p->ScribbleAst.Role(p.role) }
            is Stmt.ForYield -> res += findRoles(stmt.block)
            is Stmt.If -> res += findRoles(stmt.ifTrue) + findRoles(stmt.ifFalse)
            else -> {}
        }
        return res.toSet()
    }
}