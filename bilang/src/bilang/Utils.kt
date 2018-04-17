package bilang


fun <K, V> Map<K, List<V>>.product() : List<Map<K, V>> =
        entries.map{(key, value) -> value.map { Pair(key, it) } }.product().map { it.toMap() }

fun <T> Iterable<List<T>>.product() : List<List<T>> =
        fold(listOf(listOf()), { acc, y -> y.flatMap { t -> acc.map { tup -> tup + t } } })

object UniqueHash {
    private var n = 0
    private val m = mutableMapOf<Any, Int>()
    fun of(k: Any) : Int {
        if (!m.containsKey(k)) {
            n += 1
            m[k] = n
        }
        return m.getValue(k)
    }
}

fun <A, B> Pair<A, A>.map(f: (A) -> B): Pair<B, B> = Pair(f(first), f(second))
