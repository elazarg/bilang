package bilang

import java.util.*

internal class SymbolTable<T>(initial: MutableMap<String, T>) {
    private val scope = LinkedList<MutableMap<String, T>>(listOf(initial))

    fun push() {
        scope.addFirst(mutableMapOf())
    }

    fun pop() {
        scope.removeFirst()
    }

    fun currentScope(): MutableMap<String, T> = scope.peekFirst()

    fun lookup(v: String): T? {
        for (m in scope) {
            if (m.containsKey(v))
                return m[v]
        }
        return null
    }

    fun update(v: String, value: T) {
        for (m in scope) {
            if (m.containsKey(v)) {
                m[v] = value
                return
            }
        }
        throw RuntimeException("Undefined variable $v")
    }

    override fun toString() = scope.toString()
}