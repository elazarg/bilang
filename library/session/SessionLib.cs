using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using System.Linq;

using static CoreLib;
using static Utils;

public static class SessionLib {

    public static async Task<Connection[]> ConnectMany(string tag, Task<bool> until) {
        List<Connection> connections = new List<Connection>();
        while (!await until) {
            connections.Add(await Connect(tag));
        }
        return connections.ToArray();
    }

    public static void Notify(String declaration, params Connection[] participants) {
        CoreLib.Notify(declaration, participants.Select(x => x.address).ToArray());
    }

    public static Task<ValueTuple<Connection, T>> Connect<T>(string tag, int id = 0) where T : struct =>
        CoreLib.Connect<T>(tag, require: NoReq);

    public static Task<Connection> Connect(string tag = "", int id = 0) => Connect();
    
    public static Task<T1> Receive<T1>(this Connection c, string tag) where T1 : struct => c.Receive<T1>(tag, NoReq);

    public static async Task<ValueTuple<Connection, T1?, Connection, T2?>>
        IndependentConnection<T1, T2>(string tag1, string tag2)
        where T1 : struct
        where T2 : struct {
        ((var c1, var h1), (var c2, var h2)) = await CoreLib.Parallel(
            Connect<Hidden<T1>>("Hide1"),
            Connect<Hidden<T2>>("Hide2")
        );
        (var p1, var p2) = await CoreLib.Parallel(
            c1.Open(h1),
            c2.Open(h2)
        );
        return (c1, p1, c2, p2);
    }

    public static void Notify<T>(String declaration, params (Connection, T)[] participants) {
        Notify(declaration, participants.ToArray());
    }

    public static Task<T[]> Parallel<T>(IEnumerable<Task<T>> ts) {
        return Parallel(ts.ToArray());
    }

    public static async Task<Hidden<T1>> Hide<T1>(this Connection c) where T1 : struct {
        uint hash = await c.Receive<uint>("Hide");
        return new Hidden<T1>(hash, c.address); // should be some identity
    }

    public static async Task<T?> Open<T>(this Connection c, Hidden<T> h) where T : struct {
        var salted = await c.Receive<Hidden<T>.Salted>("Open");
        if (Tuple.Create(salted, h.owner).GetHashCode() != h.hash)
            return null;
        return salted.value;
    }

    public static async Task<ValueTuple<T1?, T2?>> Independent<T1, T2>(Connection a, Connection b)
    where T1 : struct
    where T2 : struct {
        var h = await CoreLib.Parallel(a.Hide<T1>(), b.Hide<T2>());
        return await CoreLib.Parallel(a.Open(h.Item1), b.Open(h.Item2));
    }

    public static async Task<T?[]> Independent<T>(params Connection[] ts) where T : struct {
        var hs = await Parallel(ts.Select(async a => (a, await a.Hide<T>())));
        return await Parallel(hs.Select(a => a.Item1.Open(a.Item2)));
    }

    public static async Task<T?[]> Independent<T>(IEnumerable<Connection> ts) where T : struct {
        return await Independent<T>(ts.ToArray());
    }

    public static async Task<T> AwaitOrAwait<T>(Task<T?> first, Task<T> fallback) where T : struct {
        var res = await first;
        return res ?? await fallback;
    }

}
