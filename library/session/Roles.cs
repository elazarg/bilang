
interface Dir<in From, out To> { } // "in" since we want to be covariant
interface Client { }
interface S { }

abstract class Args<T> {
    internal T _;
    public static implicit operator T(Args<T> a) { return a._; }
    public override string ToString() { return $"{GetType()}({_})"; }
}

static class ExtD {
    internal static void Deconstruct<T>(this Args<T> d, out T res) { res = d._; }
    internal static void Deconstruct<T1, T2>(this Args<(T1, T2)> d, out T1 res1, out T2 res2) { (res1, res2) = d._; }
    internal static void Deconstruct<T1, T2, T3>(this Args<(T1, T2, T3)> d, out T1 res1, out T2 res2, out T3 res3) { (res1, res2, res3) = d._; }
}
