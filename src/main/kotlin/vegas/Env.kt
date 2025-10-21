package vegas

import vegas.frontend.Exp
import vegas.frontend.Role


data class Env<T>(val g: Map<Exp.Var, T>, val r: Map<Role, T>, val h: Map<Pair<Role, Exp.Var>, T>) {
    constructor(): this(mapOf(), mapOf(), mapOf())

    operator fun plus(p: Pair<Exp.Var, T>) = Env(g + p, r, h)
    operator fun plus(p: Map<Exp.Var, T>) = Env(g + p, r, h)
    infix fun withMap(p: Map<Pair<Role, Exp.Var>, T>) = Env(g, r, h + p)
    infix fun withRole(p: Pair<Role, T>) = Env(g, r + p, h)

    fun getValue(role: Role, field: Exp.Var) = getValue(Pair(role, field))
    fun getValue(m: Pair<Role, Exp.Var>) = h.getValue(m)

    fun getValue(v: Exp.Var) = g.getValue(v)
    fun getValue(role: Role) = r.getValue(role)

    // Utils
    val Pair<Role, String>.role: Role get() = first
    val Pair<Role, String>.field: String get() = second
}
