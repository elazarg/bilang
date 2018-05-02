package bilang


fun <K, V> Map<K, List<V>>.product(): List<Map<K, V>> =
        entries.map { (key, value) -> value.map { Pair(key, it) } }.product().map { it.toMap() }

fun <T> Iterable<List<T>>.product(): List<List<T>> =
        fold(listOf(listOf()), { acc, y -> y.flatMap { t -> acc.map { tup -> tup + t } } })

object UniqueHash {
    private var n = 0
    private val m = mutableMapOf<Any, Int>()
    fun of(k: Any): Int {
        if (!m.containsKey(k)) {
            n += 1
            m[k] = n
        }
        return m.getValue(k)
    }
}

fun <A, B> Pair<A, A>.map(f: (A) -> B): Pair<B, B> = Pair(f(first), f(second))

fun <T> Iterable<T>.join(sep: String) = joinToString(sep)

fun <T> Iterable<T>.join(sep: String, f: (T) -> String) = joinToString(sep) { f(it) }

//fun <K, V, V1> Iterable<Pair<K, V>>.mapValues(f: (K, V) -> V1) : List<Pair<K, V1>> = map { (k, v) -> Pair(k, f(k, v)) }

fun <K, V, V1> Iterable<Pair<K, V>>.mapValues(f: (Pair<K, V>) -> V1) : List<Pair<K, V1>> = map { (k, v) -> Pair(k, f(Pair(k, v))) }

fun <K, V> Iterable<Map<K, V>>.union(): Map<K, V> = flatMap { it.entries.map { it.toPair() } }.toMap()

// type-specific

fun <T> Iterable<Pair<String, T>>.names() = map { (name, _) -> name }
fun <T> Iterable<Pair<String, T>>.types() = map { (_, type) -> type }

val Pair<String, TypeExp>.name: String get() = first
val Pair<String, TypeExp>.type: TypeExp get() = second
