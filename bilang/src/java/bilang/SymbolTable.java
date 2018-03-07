package bilang;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

class SymbolTable<T> {
    final private LinkedList<Map<String, T>> scope;

    SymbolTable(Map<String, T> initial) {
        this.scope = new LinkedList<>(Collections.singletonList(initial));
    }

    void push() {
        scope.addFirst(new HashMap<>());
    }

    void pop() {
        scope.removeFirst();
    }

    Map<String, T> currentScope() {
        return scope.peekFirst();
    }

    T lookup(String v) {
        for (Map<String, T> m : scope) {
            if (m.containsKey(v))
                return m.get(v);
        }
        return null;
    }

    void update(String v, T val) {
        for (Map<String, T> m : scope) {
            if (m.containsKey(v)) {
                m.put(v, val);
                return;
            }
        }
        throw new RuntimeException("Undefined variable " + v);
    }

    @Override
    public String toString() {
        return scope.toString();
    }
}