package bilang;


import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;

interface Type {
    default boolean isCompatible(Type other) {
        return this == other;
    }

    static boolean compatible(Type left, Type right) {
        return left.isCompatible(right);
    }
}

class Range implements Type {
    final int start;
    final int end;
    Range(int start, int end) {
       this.start = start;
       this.end = end;
    }

    @Override
    public boolean isCompatible(Type other) {
        if (other == this || other == Value.INT)
            return true;
        if (other instanceof Range) {
            Range range = ((Range) other);
            return range.start <= start && range.end >= end;
        }
        return false;
    }
}

class Subset implements Type {
    final private Set<Integer> items;
    Subset(Set<Integer> items) {
        this.items = items;
    }

    @Override
    public boolean isCompatible(Type other) {
        return other == this
            || other == Value.INT
            || other instanceof Range && items.stream().allMatch(x->((Range)other).start <= x && ((Range)other).end >= x)
            || other instanceof Subset && items.containsAll(((Subset) other).items);
    }
}

enum Value implements Type {
    INT,
    BOOL,
    ROLE,
    UNDEF,
}
