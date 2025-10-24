package vegas.backend.scribble

import vegas.RoleId
import vegas.frontend.GameAst
import vegas.frontend.Ext
import vegas.frontend.Kind
import vegas.frontend.Outcome
import vegas.frontend.TypeExp
import vegas.frontend.VarDec
import vegas.frontend.findRoleIds
import vegas.ir.desugar
import vegas.join
import vegas.map
import kotlin.String

fun generateScribble(p: GameAst): Sast.Protocol {
    val roles = findRoleIds(p.game)
    val types =
        p.types.map { (k, v) -> k.name to javaTypeOf(v) } + ("int" to "Integer") + ("bool" to "Boolean") + ("hidden" to "Integer")

    return Sast.Protocol(p.name, types.toMap(), roles, Sast.Block(gameToScribble(p.game, roles)))
}

private fun gameToScribble(ext: Ext, roles: Set<RoleId>): List<Sast.Action> = when (ext) {
    is Ext.BindSingle -> {
        val params = ext.q.params
        val role = ext.q.role.id

        fun send(label: String, decls: List<Pair<String, String>>, to: Set<RoleId> = setOf(SERVER)) =
            Sast.Action.Send(label, decls, role, to)

        fun sendToServer(): List<Sast.Action.Send> {
            val (priv, pub) = params.partition { (_, type) -> type is TypeExp.Hidden }.map { declsOf(it) }
            return listOfNotNull(
                send("Hidden", priv).takeUnless { priv.isEmpty() },
                send("Public", pub).takeUnless { pub.isEmpty() }
            )
        }

        val send = when (ext.kind) {
            Kind.JOIN -> listOf(Sast.Action.Connect(role)) + sendToServer()
            Kind.JOIN_CHANCE -> listOf(Sast.Action.Connect(role)) + sendToServer()
            Kind.YIELD -> sendToServer()
            Kind.REVEAL -> listOf(send("Reveal", declsOf(params)))
        }

        val broadcast = Sast.Action.Send(
            "Broadcast",
            declsOf(params.filterNot { (_, type) -> type is TypeExp.Hidden }),
            SERVER,
            roles - role
        )

        send + broadcast + gameToScribble(ext.ext, roles)
    }

    is Ext.Bind -> ext.qs.flatMap { query ->
        gameToScribble(Ext.BindSingle(ext.kind, query, Ext.Value(Outcome.Value(mapOf()))), roles)
    }.sortedBy { rankOrder(it) } + gameToScribble(ext.ext, roles)

    is Ext.Value -> desugar(ext.outcome).ts.keys.map { Sast.Action.Send("Withdraw", listOf(), it.id, setOf(SERVER)) }
}

private fun rankOrder(it: Sast.Action): Int =
    if (it is Sast.Action.Send) when (it.label) {
        "Hidden" -> 1
        "Reveal" -> 2
        else -> 3
    } else 0

private fun declsOf(params: List<VarDec>) = params.map { (v, type) -> Pair(v.id.name, typeOf(type)) }

private fun typeOf(t: TypeExp): String = when (t) {
    TypeExp.INT -> "int"
    TypeExp.BOOL -> "bool"
    TypeExp.ADDRESS -> "address"
    TypeExp.EMPTY -> throw AssertionError()
    is TypeExp.Hidden -> "hidden" //_${typeOf(t.type)}"
    is TypeExp.TypeId -> t.name
    is TypeExp.Subset -> "subset_${t.values.join("_")}"
    is TypeExp.Range -> "range_${t.min}_${t.max}"
    is TypeExp.Opt -> "opt_${t.type}"
}

private fun javaTypeOf(t: TypeExp): String = when (t) {
    TypeExp.INT -> "Integer"
    TypeExp.BOOL -> "Boolean"
    TypeExp.ADDRESS -> "Integer"
    TypeExp.EMPTY -> throw AssertionError()
    is TypeExp.Hidden -> "Integer"
    is TypeExp.TypeId -> t.name
    is TypeExp.Subset -> "Integer"
    is TypeExp.Range -> "Integer"
    is TypeExp.Opt -> "Object"
}
