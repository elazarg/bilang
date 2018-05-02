package bilang


data class Env<T>(val g: Map<String, T>, val h: Map<Pair<String, String>, T>) {
    constructor(): this(mapOf(), mapOf())

    operator fun plus(p: Pair<String, T>) = Env(g + p, h)
    operator fun plus(p: Map<String, T>) = Env(g + p, h)
    infix fun with(p: Map<Pair<String, String>, T>) = Env(g, h + p)
    infix fun with(p: Pair<Pair<String, String>, T>) = Env(g, h + p)

    fun getValue(role: String, field: String) = h.getValue(Pair(role, field))

    fun getValue(v: String) = g.getValue(v)

    // Utils
    val Pair<String, String>.role: String get() = first
    val Pair<String, String>.field: String get() = second
}
