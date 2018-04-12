package bilang


fun <K, V> Map<K, List<V>>.product() : List<Map<K, V>> =
        entries.map{(key, value) -> value.map { Pair(key, it) } }.product().map{it.toMap()}

fun <T> Iterable<List<T>>.product() : List<List<T>> =
        fold(listOf(listOf()), { acc, y -> y.flatMap { t -> acc.map { tup -> tup + t } } })

fun main(args: Array<String>) {
    println(listOf(listOf(1, 2, 3), listOf(1, 2, 3)).product())
    println(mapOf(
            Pair("a", listOf(1, 2, 3)),
            Pair("b", listOf(4, 5, 6)),
            Pair("c", listOf(7, 8, 9))
    ).product())
}