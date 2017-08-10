using System;
using System.Threading.Tasks;

using static Utils;

public static class CoreLib {
    static dynamic UNKOWN = null;
    static Connection connector = UNKOWN;

    public static async Task<(Connection, T)> Connect<T>(string tag, Func<T, bool> require, uint? id = null) where T : struct {
        uint connected_id;
        if (id == null) {
            connected_id = await connector.Receive<uint>(tag: tag);
        } else {
            Notify("Would you like to connect?", (uint)id);
            connected_id = await connector.Receive<uint>(tag: tag, require: cid => cid == id);
        }
        return UNKOWN; // new ConnectionImp<T>(connected_id);
    }
    
    public static void Declare(String declaration, params Connection[] participants) {}
    public static void Notify(String declaration, params uint[] participants) { }
    public static void Publish(String declaration) {    }
    public static void Pay(Connection t, params Money[] ms) { }

    public struct Money {
        public int amount;
    }

    public struct Connection : IDisposable {
        public uint address;
        
        public async Task<T> Receive<T>(string tag, Func<T, bool> require) where T : struct {
            return await UNKOWN;
        }

        public void Dispose() {
            Notify("Session ended", address);
        }
    }

    #region Combinators

    public static Task<ValueTuple<T1, T2>> Parallel<T1, T2>(Task<T1> t1, Task<T2> t2) where T1: struct where T2: struct {
        return UNKOWN;
    }
    public static Task<ValueTuple<T1?, T2?>> Parallel<T1, T2>(Task<T1?> t1, Task<T2?> t2) where T1 : struct where T2 : struct {
        return UNKOWN;
    }
    public static async Task<T[]> Parallel<T>(params Task<T>[] ts) {
        dynamic t = null;
        return await t;
    }

    public static async Task<dynamic> FirstOf(params Task[] ts) {
        return await UNKOWN;
    }

    public static async Task<DPair<Connection, Connection>> Parallel(Task<Connection> t1, Task<Connection> t2) {
        return await UNKOWN;
    }

#endregion

}
