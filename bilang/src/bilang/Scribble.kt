package bilang

typealias Role = String

sealed class Sast {

    data class Protocol(val name: String, val types: Map<String, String>, val roles: Set<Role>, val block: Block) : Sast()

    data class Block(val stmts: List<Action>) : Sast()

    sealed class Action : Sast() {
        data class Send(val label: String, val params: List<Pair<String, String>>, val from: Role, val to: Set<Role>?) : Action()
        data class Connect(val to: Role) : Action()
        data class Choice(val at: Role, val choices: List<Block>) : Action()
        data class Rec(val label: String, val actions: Block) : Action()
        data class Continue(val label: String) : Action()
    }

}

fun Sast.Protocol.prettyPrintAll(): String {
    val typedecls = types.map {"""type <java> "java.lang.${it.value}" from "rt.jar" as ${it.key};"""}.join("\n")
    val items = listOf("module Game;", typedecls, prettyPrint()) + (roles + "Server").map { prettyPrint(it) }
    return items.join("\n\n")
}

fun Sast.prettyPrint(role: String? = null, indent: Int = 0, connected: Set<Role> = setOf()): String {
    fun pretty(x: Sast) = x.prettyPrint(role, indent, connected)
    val code = when (this) {
        is Sast.Protocol -> {
            assert(indent == 0)
            val ps = roles.join(", ") { "role $it" }
            when (role) {
                null -> "explicit global protocol $name(role Server, $ps)"
                "Server" -> "local protocol ${name}_Server(role Server, $ps)"
                else -> "local protocol ${name}_$role(role Server, role $role)"
            } + pretty(block)
        }
        is Sast.Block -> stmts
                .map { it.prettyPrint(role, indent + 1, if (it is Sast.Action.Connect) connected + it.to else connected) }
                .filter { it.isNotBlank() }
                .joinToString(";\n", "{\n", ";\n${"    ".repeat(indent)}}\n")
        is Sast.Action.Send -> {
            var res = if (params.isEmpty()) "$label()" else "${label}_${params.names().join("_")}(${params.types().join(", ")})"
            if (role == null || to == null || role in to)
                res += " from $from"
            if (to != null && (role == null || from == role))
                res += " to ${to.join(", ")}"
            if (" to " in res || " from " in res) res
            else ""
        }
        is Sast.Action.Connect ->
            when (role) {
                null -> "connect Server to $to"
                to -> "connect Server"
                else -> ""
            }
        is Sast.Action.Choice -> {
            val blocks = choices.join(" or ") { pretty(it) }
            "choice at $at $blocks"
        }
        is Sast.Action.Rec -> "rec " + pretty(actions)
        is Sast.Action.Continue -> "continue $label"
    }
    return "    ".repeat(indent) + code
}

fun programToScribble(p: ExpProgram): Sast.Protocol {
    val roles = findRoles(p.game).toSet()
    val types = p.types.mapValues { (_, v) -> javaTypeOf(v) } + Pair("int", "Integer") + Pair("bool", "Boolean")

    return Sast.Protocol(p.name, types, roles, Sast.Block(gameToScribble(p.game, roles)))
}

private fun gameToScribble(ext: Ext, roles: Set<Role>): List<Sast.Action> = when (ext) {
    is Ext.BindSingle -> {
        val params = ext.q.params
        val role = ext.q.role
        fun send(label: String, decls: List<Pair<String, String>>, to: Set<Role> = setOf("Server")) =
                Sast.Action.Send(label, decls, role, to)
        fun sendToServer(): List<Sast.Action.Send> {
            val (priv, pub) = params.partition { (_, type) -> type is TypeExp.Hidden }.map { declsOf(it) }
            return listOfNotNull(
                    send("Hidden", priv).takeUnless { priv.isEmpty() },
                    send("Public", pub).takeUnless { pub.isEmpty() }
            )
        }

        (when (ext.kind) {
            Kind.JOIN -> listOf(Sast.Action.Connect(role)) + sendToServer()
            Kind.JOIN_CHANCE -> listOf(Sast.Action.Connect(role)) + sendToServer()
            Kind.YIELD -> sendToServer()
            Kind.REVEAL -> listOf(send("Reveal", declsOf(params)))
            Kind.MANY -> TODO()
        } + Sast.Action.Send("Broadcast", declsOf(params.filterNot { (_, type) -> type is TypeExp.Hidden }), "Server", roles - role)
        + gameToScribble(ext.ext, roles))
    }

    is Ext.Bind -> ext.qs.flatMap { query ->
        gameToScribble(Ext.BindSingle(ext.kind, query, Ext.Value(Outcome.Value(mapOf()))), roles)
    }.sortedBy { rankOrder(it) } + gameToScribble(ext.ext, roles)

    is Ext.Value -> ext.exp.ts.keys.map { Sast.Action.Send("Withdraw", listOf(), it, setOf("Server")) }
}

private fun rankOrder(it: Sast.Action): Int =
        if (it is Sast.Action.Send) when (it.label) {
            "Hidden" -> 1
            "Reveal" -> 2
            else -> 3
        } else 0

private fun declsOf(params: List<VarDec>) = params.mapValues { (_, type) -> typeOf(type) }

private fun typeOf(t: TypeExp): String = when (t) {
    TypeExp.INT -> "int"
    TypeExp.BOOL -> "bool"
    TypeExp.ROLE -> "role"
    TypeExp.ROLESET -> "roleset"
    TypeExp.ADDRESS -> "address"
    is TypeExp.Hidden -> "hidden_${typeOf(t.type)}"
    is TypeExp.TypeId -> t.name
    is TypeExp.Subset -> "subset_${t.values.join("_")}"
    is TypeExp.Range -> "range_${t.min}_${t.max}"
    is TypeExp.Opt -> "opt_${t.type}"
}

private fun javaTypeOf(t: TypeExp): String = when (t) {
    TypeExp.INT -> "Integer"
    TypeExp.BOOL -> "Boolean"
    TypeExp.ROLE -> TODO()
    TypeExp.ROLESET -> TODO()
    TypeExp.ADDRESS -> "Integer"
    is TypeExp.Hidden -> "Integer"
    is TypeExp.TypeId -> t.name
    is TypeExp.Subset -> "Integer"
    is TypeExp.Range -> "Integer"
    is TypeExp.Opt -> "Object"
}
