package bilang;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

class SymbolTable {
    final private LinkedList<Map<String, Type>> scope;

    SymbolTable(Map<String, Type> initial) {
        this.scope = new LinkedList<>(Collections.singletonList(initial));
    }

    void push() {
        scope.addFirst(new HashMap<>());
    }

    void pop() {
        scope.removeFirst();
    }

    Map<String, Type> currentScope() {
        return scope.peekFirst();
    }

    Type lookup(String text) {
        for (Map<String, Type> m : scope) {
            if (m.containsKey(text))
                return m.get(text);
        }
        return null;
    }
}