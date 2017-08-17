using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading.Tasks;
using System.Threading.Tasks.Schedulers;
using static System.Console;


static class Playground {
#region lib
    abstract class D<T> {
        internal T _;
        public static implicit operator T(D<T> a) { return a._; }
        public override string ToString() { return $"{GetType()}{_}"; }
    }
    static void Deconstruct<T>(this D<T> d, out T res) { res = d._; }
    static void Deconstruct<T1, T2>(this D<(T1, T2)> d, out T1 res1, out T2 res2) { (res1, res2) = d._; }
    static void Deconstruct<T1, T2, T3>(this D<(T1, T2, T3)> d, out T1 res1, out T2 res2, out T3 res3) { (res1, res2, res3) = d._; }

#endregion
    private sealed class Question : D<int>      { internal Question(int _1)       { _ = _1;       } }
    private sealed class Answer : D<(int, int)> { internal Answer(int _1, int _2) { _ = (_1, _2); } }

    private interface Response { }
    private sealed class Accepted : Response { }
    private sealed class Rejected : Response { }


    static async Task ClientQuestion(uint address) {
        var link = new PrivateLink(bc, address, serverAddress);       WriteLine($"Client Q sends question");
        await link.SendAsync(new Question(15));
        var (m, n) = await link.Receive<Answer>();                    WriteLine($"Client Q received solution ({m}, {n})");
                                                                      WriteLine($"Client Q done");
    }

    static async Task ClientAnswer(uint address) {
        var link = new PrivateLink(bc, address, serverAddress);       WriteLine($"Client A fetches question");
        int riddle = await link.Receive<Question>();                  WriteLine($"Client A sends solution {(3, 5)}");
        // pretend we are solving the problem
        await link.SendAsync(new Answer(3, 5));                       WriteLine($"Client A sent solution");
        switch (await link.Receive<Response>()) {
            case Accepted x: WriteLine("Good answer"); break;
            case Rejected x: WriteLine("Bad answer"); break;
            default: Debug.Assert(false); break;
        }
                                                                      WriteLine($"Client A done");
    }

    static async Task Server(uint address) {
        var pub = new PublicLink(bc, address);                                 WriteLine($"Server is waiting for connection");
        (var asker, int riddle) = await pub.Connection<Question>();            WriteLine($"Server received {riddle} from {asker}");
        // publishing without waiting does not work with single point for pending/delivered
        // it should be extracted out to the clients, or as a public state
        pub.Publish(new Question(riddle));                                     WriteLine("Server receives...");
        while (true) {
            var (solver, (m, n)) = await pub.Connection<Answer>();             WriteLine($"Server received {m} {n} from {solver}");
            if (m * n == riddle) {
                solver.Send(new Accepted());
                asker.Send(new Answer(3, 5));                                  WriteLine("Server done");
                break;
            } else {
                solver.Send(new Rejected());
            }
        }
    }

    static BC bc;
    const uint serverAddress = 1;

    static TaskFactory factory = new TaskFactory(new OrderedTaskScheduler());

    public static void Start(Task t) {
        factory.StartNew(t.RunSynchronously);
    }

    public static void Main() {
        bc = new BC(1, 2, 3);
        Start(Server(1));
        Start(ClientQuestion(2));
        Start(ClientAnswer(3));

        Console.ReadKey();
    }
}

class BC {

    public class Metadata {
        public uint sender;
        // null means everyone
        public uint? target;
        public volatile bool pending = true;
        public override string ToString() => $"{sender} -> {target} ({pending})";
    }
    List<(object, Metadata)> publications = new List<(object, Metadata)>();

    public BC(params uint[] addresses) {
    }

    public void Publish(object payload, Metadata info) {
        lock (this) {
            publications.Add((payload, info));
        }
    }

    public async Task PublishAsync(object payload, Metadata info) {
        Publish(payload, info);
        while (info.pending) {
            await Task.Yield();
        }
    }
    
    public async Task<(uint, T)> Receive<T>(Func<object, Metadata, (bool, T)> p) {
        while (true) {
            lock (this) {
                foreach (var (payload, info) in publications) {
                    if (info.pending) {
                        var (ok, res) = p(payload, info);
                        if (ok) {
                            info.pending = false;
                            return (info.sender, res);
                        }
                    }
                }
            }
            await Task.Yield();
        }
    }
}

struct Nothing { }

/// <summary>
///  Helper class: one side of a binary channel, hides some ugly parameters
/// </summary>
abstract class Link {
    protected BC bc;
    protected uint address;

    public Link(BC bc, uint address) {
        this.address = address;
        this.bc = bc;
    }

    protected (bool, T) f<T>(object payload, BC.Metadata info) {
        if (info.target != null && info.target != address)
            return (false, default);
        try {
            return (true, (T)payload);
        } catch (InvalidCastException) {
            return (false, default);
        }
    }
}

class PrivateLink : Link {
    uint target;

    public PrivateLink(BC bc, uint address, uint target) : base(bc, address) {
        this.target = target;
    }
    
    public async Task<T> Receive<T>() {
        (uint _, T v) = await bc.Receive(f<T>);
        return v;
    }

    public async Task SendAsync<T>(T payload) {
        await bc.PublishAsync(payload, new BC.Metadata() { sender = address, target = target });
    }

    public void Send<T>(T payload) {
        bc.Publish(payload, new BC.Metadata() { sender = address, target = target });
    }
}

class PublicLink : Link {
    public PublicLink(BC bc, uint address) : base(bc, address) {
    }

    public async Task<(PrivateLink, T)> Connection<T>() {
        (uint addr, T val) = await bc.Receive(f<T>);
        return (new PrivateLink(bc, address, addr), val);
    }

    public void Publish(object payload) {
        bc.Publish(payload, new BC.Metadata() { sender = address, target = null });
    }
    public async Task PublishAsync(object payload) {
        await bc.PublishAsync(payload, new BC.Metadata() { sender = address, target = null });
    }
}
