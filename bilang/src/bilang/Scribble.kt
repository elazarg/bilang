package bilang

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
    data class Role(val name: String)
    data class VarDec(val name: String, val type: Type)
}

fun Sast.prettyPrint(role: String? = null, indent: Int = 0): String {
    fun pretty(x: Sast) = x.prettyPrint(role, indent)
    val code = when (this) {
        is Sast.Protocol -> {
            assert(indent == 0)
            val ps = ", " + roles.joinToString(", ") { "role ${it.name}" }
            val scope = if (role == null) "global" else "local"
            "explicit $scope protocol MyProtocol_$role(role Server$ps) " + pretty(block)
        }
        is Sast.Block -> stmts
                .map { it.prettyPrint(role, indent + 1) }
                .filter { it.isNotBlank() }
                .joinToString(";\n", "{\n", ";\n${"    ".repeat(indent)}}\n")
        is Sast.Action.Send -> {
            val args = params.joinToString(", ") { it.type.name }
            val names = params.joinToString("_") { it.name }
            var res = if (params.isEmpty()) "$label()" else "${label}_$names($args)"
            if (role == null || to.contains(Sast.Role(role)))
                res += " from ${from.name}"
            if (role == null || from.name == role)
                res += " to ${to.joinToString(", ") { it.name }}"
            res
        }
        is Sast.Action.Connect ->
            when (role) {
                null -> "connect Server to ${to.name}"
                to.name -> "connect Server"
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
    val roles = findRoles(p.game).map { Sast.Role(it) }.toSet()
    return Sast.Protocol(roles, Sast.Block(gameToScribble(p.game, roles)))
}

private val server = Sast.Role("Server")

private fun gameToScribble(ext: Ext, roles: Set<Sast.Role>): List<Sast.Action> = when (ext) {
    is Ext.BindSingle -> {
        val params = ext.q.params
        val role = Sast.Role(ext.q.role.name)
        fun send(label: String, decls: List<Sast.VarDec>, to: Set<Sast.Role> = setOf(server)) = Sast.Action.Send(label, decls, role, to)
        var res = listOf<Sast.Action>()
        when (ext.q.kind) {
            Kind.JOIN ->
                res += Sast.Action.Connect(role)
            Kind.YIELD -> {
                val (priv, pub) = params.partition { p -> p.type is TypeExp.Hidden }.map { declsOf(it) }
                res += actions(pub, send("Public", pub))
                res += actions(priv, send("Hidden", priv))
            }
            Kind.REVEAL ->
                res += send("Reveal", declsOf(params))
            Kind.MANY -> TODO()
        }


        res += Sast.Action.Send("Broadcast", declsOf(params.filterNot { it.type is TypeExp.Hidden }), server, roles - role)
        res += gameToScribble(ext.exp, roles)
        res
    }

    is Ext.Bind -> ext.qs.flatMap { query ->
        gameToScribble(Ext.BindSingle(query, Ext.Value(Exp.UNDEFINED)), roles)
    }.sortedBy { rankOrder(it) } + gameToScribble(ext.exp, roles)

    is Ext.Value -> listOf()
}

private fun rankOrder(it: Sast.Action): Int =
        if (it is Sast.Action.Send) when (it.label) {
            "Hidden" -> 1
            "Reveal" -> 2
            else -> 3
        } else 0

private fun actions(publicDecls: List<Sast.VarDec>, action: Sast.Action.Send) =
        if (publicDecls.isEmpty()) listOf() else listOf(action)

private fun declsOf(params: List<VarDec>) = params.map {
    Sast.VarDec(it.name.name, Sast.Type(typeOf(it.type)))
}

private fun typeOf(t: TypeExp): String = when (t) {
    TypeExp.INT -> "int"
    TypeExp.BOOL -> "bool"
    TypeExp.ROLE -> "role"
    TypeExp.ROLESET -> "roleset"
    TypeExp.ADDRESS -> "address"
    TypeExp.UNIT -> "unit"
    is TypeExp.Hidden -> "hidden_${typeOf(t.type)}"
    is TypeExp.TypeId -> t.name
    is TypeExp.Subset -> "subset_${t.values.joinToString("_")}"
    is TypeExp.Range -> "range_${t.min}_${t.max}"
    is TypeExp.Opt -> "opt_${t.type}"
}
