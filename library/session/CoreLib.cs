using System;
using System.Threading;
using System.Threading.Tasks;
using System.Threading.Tasks.Dataflow;

using static Utils;

public static class CoreLib {
    static dynamic UNKOWN = null;
    static Connection connector = UNKOWN;

    public static async Task<(Connection, T)> Connect<T>(string tag, Func<T, bool> require, uint? id = null) where T : struct {
        return (new Connection(VM.WaitForClientConnection(tag)), default(T));
        /*
        uint connected_id;
        if (id == null) {
            connected_id = await connector.Receive<uint>(tag: tag);
        } else {
            Notify("Would you like to connect?", (uint)id);
            connected_id = await connector.Receive<uint>(tag: tag, require: cid => cid == id);
        }
        return UNKOWN; // new ConnectionImp<T>(connected_id);
        */
    }
    
    public static void Declare(String declaration, params Connection[] participants) {}
    public static void Notify(String declaration, params uint[] participants) { }
    public static void Publish<T>(String declaration, T value) where T: struct {    }
    public static void Pay(Connection t, params Money[] ms) { }
    public static void Require(bool v) { }

    public struct Money {
        public int amount;
        private int v;

        public Money(int v=0) : this() {
            this.v = v;
        }
    }

    public struct Connection : IDisposable {
        public readonly uint address;
        public Connection(uint address) {
            this.address = address;
        }
        
        public async Task<T> Receive<T>(string tag, Func<T, bool> require) where T : struct {
            return await UNKOWN;
        }
        public async Task Receive(string tag) {
            
        }
        public async Task<T> Receive<T, Param>(string tag, Func<T, bool> require, Param args) where T : struct {
            return await UNKOWN;
        }
        public Connection Notify<T>(T value) {
            return this;
        }
        public Connection Notify<T>(string tag, T value) {
            return this;
        }
        public void Dispose() {
            Notify("Session ended");
        }
    }

    #region Combinators

    public static Task<ValueTuple<T1, T2>> Parallel<T1, T2>(Task<T1> t1, Task<T2> t2) where T1: struct where T2: struct {
        return UNKOWN;
    }

    public static Task<ValueTuple<T1?, T2?>> Parallel<T1, T2>(Task<T1?> t1, Task<T2?> t2) where T1 : struct where T2 : struct {
        return UNKOWN;
    }

    /***
     * Gotcha: If we really want it to be done in parallel, we probably also want it to be 
     * "transactional", i.e. all VISIBLE commands must be either performed completely or not at all.
     * This is not expressed in the type, so it is not compositional without "looking inside"
     * the parameters ts.
     * 
     * So the signature is good for receiving data, (assuming the sending itself is not leaking data)
     * and for connecting. It is less so for money transfer, since reversing it (returning the money)
     * does not cancel it (since there was a period of time without the money in the bank).
     * 
     * For example, the following is not straight forward at all:
     * 
     *     Contract C = "lawyer-like blah blah";
     *     await Parallel(a.Sign(C), b.Sign(C));
     *     
     * Since the (likely) intention of the programmer is that a will sign C if and only if b will sign C.
     * But a naive implementation will wait for both to sign, so there will be a time when only one did.
     * A better implementation will wait for one and do nothing, wait for the other and do nothing,
     * and the calling site will retrieve the fact that it is signed by both. So we manually perform
     * the logical step from
     *
     *     
     *     forall X, (b.m -> a.X) -> a.X
     *     forall Y, (a.m -> b.Y) -> b.Y
     *     
     *     
     * to 
     * 
     *     a.M and b.M
     * 
     * It cannot work at all with tasks that leak information, but this is why we have `Independent`.
     * If we have declarations and notifications in the task, they need to be performed "tentatively"
     * somehow, registered to be committed, and cannot be act upon.
     * 
     * For notifications, it turns
     *     Notify A that B occured
     * into 
     *     Notify A that a future commitment C will mean that B occured
     * 
     * So, accumulating the actions-be-performed (monad-style?) will be helpful.
     */
    public static async Task<T[]> Parallel<T>(params Task<T>[] ts) {
        dynamic t = null;
        return await t;
    }

    public static async Task<dynamic> FirstOf(params Task[] ts) {
        return await UNKOWN;
    }
    public struct Either<T1, T2> where T1: struct where T2: struct {

    }
    public static async Task<Either<T1, T2>> FirstOf<T1, T2>(Task<T1> t1, Task<T2> t2) where T1: struct where T2: struct {
        return await UNKOWN;
    }
    public static async Task<T?> FirstOf<T>(Task<T> t1, Task t2) where T : struct {
        return await UNKOWN;
    }

    public static async Task<DPair<Connection, Connection>> Parallel(Task<Connection> t1, Task<Connection> t2) {
        return await UNKOWN;
    }

#endregion

}
