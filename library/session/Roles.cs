using System;
using System.Threading.Tasks;


interface Dir<out From, in To> { } // "in" since we want to be covariant
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

struct Nothing { }

class UpLink<From> {
    public readonly uint address;
    private readonly BC bc;
    private int last = 0;

    public UpLink(BC bc, uint address, uint target) {
        this.address = address;
        this.bc = bc;
        bc.requests.Register(address);
    }

    public async Task<T> ReceiveEarliest<T>(bool @public=false) where T : Dir<S, From> {
        // retrieves the oldest message since the last one received
        //Console.WriteLine($"Client {address} receives");
        while (true) {
            for (; last < bc.events.Count; last++) {
                object obj_payload = bc.events[last];
                try {
                    (uint? to, object payload) = (Packet)obj_payload;
                    if (to == address || @public && to == null) {
                        last++;
                        return (T)payload;
                    } else {
                    }
                } catch (InvalidCastException) {
                }
            }
            await Task.Yield();
        }
    }

    public async Task SendAsync<T>(T payload) where T : Dir<From, S> {
        await bc.requests.SendRequestAsync(address, payload);
    }
    public async Task SendAsync() {
        await bc.requests.SendRequestAsync(address, new Nothing());
    }
    public void Send<T>(T payload) where T : Dir<From, S> {
        bc.requests.SendRequest(address, payload);
    }
}

class PublicLink {
    public readonly uint address;
    protected BC bc;

    public PublicLink(BC bc, uint address) {
        this.address = address;
        this.bc = bc;
    }
    
    public async Task<(DownLink<To>, T)> Connection<T, To>() {
        while (true) {
            (uint? sender, object payload) = await bc.requests.ReceiveRequest();
            try {
                return (new DownLink<To>(bc, address, (uint)sender), (T)payload);
            } catch (InvalidCastException) {
            }
        }
    }

    public async Task<DownLink<To>> Connection<To>() {
        return (await Connection<Nothing, To>()).Item1;
    }

    public void Publish<T>(T payload) where T : Dir<S, Client> {
        bc.events.Add(new Packet(null, payload));
    }
}

class DownLink<To> {
    public readonly uint target;
    public readonly uint address;
    private readonly BC bc;

    public DownLink(BC bc, uint address, uint target) {
        this.target = target;
        this.address = address;
        this.bc = bc;
    }

    public async Task<T> Receive<T>() where T : Dir<To, S> {
        while (true) {
            (uint? sender, object payload) = await bc.requests.ReceiveRequest();
            try {
                if (sender == target)
                    return (T)payload;
            } catch (InvalidCastException) {
            }
        }
    }
    
    public void Send<T>(T payload) where T : Dir<S, To> {
        bc.events.Add(new Packet(target, payload));
    }
}


static class Combinators {
    public static async Task<(T1, T2)> Parallel<T1, T2>(Task<T1> t1, Task<T2> t2) {
        System.Threading.Tasks.Parallel.Invoke(async () => await t1, async () => await t2);
        return (t1.Result, t2.Result);
    }
}