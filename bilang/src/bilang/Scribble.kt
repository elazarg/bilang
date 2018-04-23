package bilang

typealias Role = String
sealed class Sast {

    data class Protocol(val roles: Set<Role>, val block: Block) : Sast()

    data class Block(val stmts: List<Action>) : Sast()

    sealed class Action : Sast() {
        data class Send(val label: String, val params: List<VarDec>, val from: Role, val to: Set<Role>) : Action()
        data class Connect(val to: Role) : Action()
        data class Choice(val at: Role, val choices: List<Block>) : Action()
        data class Rec(val label: String, val actions: Block) : Action()
        data class Continue(val label: String) : Action()
    }

    data class Type(val name: String)
    data class VarDec(val name: String, val type: Type)
}

fun Sast.Protocol.prettyPrintAll(): String =
        (listOf(prettyPrint()) + roles.map { prettyPrint(it) }).joinToString("\n\n")

fun Sast.prettyPrint(role: String? = null, indent: Int = 0): String {
    fun pretty(x: Sast) = x.prettyPrint(role, indent)
    val code = when (this) {
        is Sast.Protocol -> {
            assert(indent == 0)
            val relevantRoles = if (role == null) roles else setOf(role)
            val ps = ", " + relevantRoles.joinToString(", ") { "role $it" }
            val scope = if (role == null) "global" else "local"
            val roletext = if (role == null) "" else "_$role"
            "explicit $scope protocol MyProtocol$roletext(role Server$ps) " + pretty(block)
        }
        is Sast.Block -> stmts
                .map { it.prettyPrint(role, indent + 1) }
                .filter { it.isNotBlank() }
                .joinToString(";\n", "{\n", ";\n${"    ".repeat(indent)}}\n")
        is Sast.Action.Send -> {
            val args = params.joinToString(", ") { it.type.name }
            val names = params.joinToString("_") { it.name }
            var res = if (params.isEmpty()) "$label()" else "${label}_$names($args)"
            if (role == null || to.contains(role))
                res += " from $from"
            if (role == null || from == role)
                res += " to ${to.joinToString(", ")}"
            if (res.contains(" to ") || res.contains(" from ")) res
            else ""
        }
        is Sast.Action.Connect ->
            when (role) {
                null -> "connect Server to $to"
                to -> "connect Server"
                else -> ""
            }
        is Sast.Action.Choice -> {
            val blocks = choices.joinToString(" or ") { pretty(it) }
            "choice at $at $blocks"
        }
        is Sast.Action.Rec -> "rec " + pretty(actions)
        is Sast.Action.Continue -> "continue $label"
    }
    return "    ".repeat(indent) + code
}

fun programToScribble(p: ExpProgram): Sast.Protocol {
    val roles = findRoles(p.game).toSet()
    return Sast.Protocol(roles, Sast.Block(gameToScribble(p.game, roles)))
}

private fun gameToScribble(ext: Ext, roles: Set<Role>): List<Sast.Action> = when (ext) {
    is Ext.BindSingle -> {
        val params = ext.q.params
        val role = ext.q.role.name
        fun send(label: String, decls: List<Sast.VarDec>, to: Set<Role> = setOf("Server")) = Sast.Action.Send(label, decls, role, to)
        fun sendToServer(): List<Sast.Action.Send> {
            val (priv, pub) = params.partition { p -> p.type is TypeExp.Hidden }.map { declsOf(it) }
            return listOfNotNull(
                    send("Hidden", priv).takeUnless { priv.isEmpty() },
                    send("Public", pub).takeUnless { pub.isEmpty() }
            )
        }

        (when (ext.kind) {
            Kind.JOIN -> listOf(Sast.Action.Connect(role)) + sendToServer()
            Kind.YIELD -> sendToServer()
            Kind.REVEAL -> listOf(send("Reveal", declsOf(params)))
            Kind.MANY -> TODO()
        } + Sast.Action.Send("Broadcast", declsOf(params.filterNot { it.type is TypeExp.Hidden }), "Server", roles - role)
        + gameToScribble(ext.ext, roles))
    }

    is Ext.Bind -> ext.qs.flatMap { query ->
        gameToScribble(Ext.BindSingle(ext.kind, query, Ext.Value(Payoff.Value(mapOf()))), roles)
    }.sortedBy { rankOrder(it) } + gameToScribble(ext.ext, roles)

    is Ext.Value -> ext.exp.ts.keys.map { Sast.Action.Send("Withdraw", listOf(), it, setOf("Server")) }
}

private fun rankOrder(it: Sast.Action): Int =
        if (it is Sast.Action.Send) when (it.label) {
            "Hidden" -> 1
            "Reveal" -> 2
            else -> 3
        } else 0

private fun declsOf(params: List<VarDec>) = params.map {
    Sast.VarDec(it.name.name, Sast.Type(typeOf(it.type)))
}

private fun typeOf(t: TypeExp): String = when (t) {
    TypeExp.INT -> "int"
    TypeExp.BOOL -> "bool"
    TypeExp.ROLE -> "role"
    TypeExp.ROLESET -> "roleset"
    TypeExp.ADDRESS -> "address"
    is TypeExp.Hidden -> "hidden_${typeOf(t.type)}"
    is TypeExp.TypeId -> t.name
    is TypeExp.Subset -> "subset_${t.values.joinToString("_")}"
    is TypeExp.Range -> "range_${t.min}_${t.max}"
    is TypeExp.Opt -> "opt_${t.type}"
}
