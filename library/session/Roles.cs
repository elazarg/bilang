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
    readonly BC bc;
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


abstract class Link {
    public readonly uint address;
    public readonly uint? target;
    public readonly BC bc;
    protected Link(uint address, uint? target, BC bc) {
        this.address = address;
        this.target = target;
        this.bc = bc;
    }
}

class PublicLink : Link {
    public PublicLink(BC bc, uint address) : base(address, null, bc) {    }
    public Connector<T, To> Connection<T, To>() => new Connector<T, To>(){link = this};
    public Connector<Nothing, To> Connection<To>() => Connection<Nothing, To>();

    public void Publish<T>(T payload) where T : Dir<S, Client> {
        bc.events.Add(new Packet(null, payload));
    }
}

class DownLink<To> : Link {
    public DownLink(BC bc, uint address, uint target) : base(address, target, bc) {
    }

    public Receiver<T> Receive<T>() where T : Dir<To, S> => new Receiver<T>() { link=this };

    public void Send<T>(T payload) where T : Dir<S, To> {
        bc.events.Add(new Packet(target, payload));
    }
}

abstract class Acceptor<T> {
    public Link link;
    public abstract (bool, T) TryAccept(uint? sender, object payload);

    private async Task<T> Accept() {
        while (true) {
            (uint? sender, object payload) = await link.bc.requests.ReceiveRequest();
            var (ok, res) = TryAccept(sender, payload);
            if (!ok)
                continue;
            return res;
        }
    }

    public System.Runtime.CompilerServices.TaskAwaiter<T> GetAwaiter() {
        return Accept().GetAwaiter();
    }
}

class Connector<T, To>: Acceptor<(DownLink<To>, T)> {
    public override (bool, (DownLink<To>, T)) TryAccept(uint? sender, object payload) {
        try {
            return (true, (new DownLink<To>(link.bc, link.address, (uint)sender), (T)payload));
        } catch (InvalidCastException) {
        }
        return (false, default);
    }
}

class Receiver<T> : Acceptor<T> {
    public override (bool, T) TryAccept(uint? sender, object payload) {
        try {
            if (sender == link.target) {
                return (true, (T)payload);
            }
        } catch (InvalidCastException) {
        }
        return (false, default);
    }
}


static class Combinators {
    public static async Task<(T1, T2)> Parallel<T1, T2>(Acceptor<T1> t1, Acceptor<T2> t2) {
        BC bc = t1.link.bc;
        T1 left = default;        bool doneLeft = false;
        T2 right = default;       bool doneRight = false;
        while (!doneLeft || !doneRight) {
            (uint? sender, object payload) = await bc.requests.ReceiveRequest();
            var (ok1, p1) = t1.TryAccept(sender, payload);
            var (ok2, p2) = t2.TryAccept(sender, payload);
            if (ok1 && !doneLeft) {
                left = p1;
                doneLeft = true;
            } else if (ok2 && !doneRight) {
                right = p2;
                doneRight = true;
            } else {
                Console.WriteLine("Dropped packets");
            }
        }
        return (left, right);
    }
}