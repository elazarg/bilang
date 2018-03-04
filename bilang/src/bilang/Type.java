package bilang;


import java.util.List;
import java.util.Map;

interface Type {
    default boolean isCompatible(Type other) {
        return this == other;
    }

    static boolean compatible(Type left, Type right) {
        return left.isCompatible(right);
    }
}

enum Value implements Type {
    VOID,
    INT,
    UNDEF,
}
