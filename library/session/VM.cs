using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using System.Threading.Tasks.Schedulers;


class Playground {
    [Flags]
    enum Tag {
        PlayerA, PlayerB, Question, Answer, Accepted, Rejected
    }

    static async Task ClientQuestion(uint address) {
        var link = new Link<Tag>(bc, address, serverAddress);       Console.WriteLine($"Client {address} sends question");
        await link.SendAsync(Tag.PlayerA, 15);
        var (m, n) = await link.Receive<(int, int)>(Tag.Answer);    Console.WriteLine($"Client {address} received solution ({m}, {n})");
    }

    static async Task ClientAnswer(uint address) {
        var link = new Link<Tag>(bc, address, serverAddress);        Console.WriteLine($"Client {address} fetches question");
        var riddle = await link.Receive<int>(Tag.Question);          Console.WriteLine($"Client {address} sends solution {(3, 5)}");
        // pretend we are solving the problem
        await link.SendAsync(Tag.PlayerB, (3, 5));                   Console.WriteLine($"Client {address} done");
        //var response = await link.Receive<Nothing>(Tag.Accepted | Tag.Rejected);
    }

    static async Task Server(uint address) {
        var pub = new PublicLink<Tag>(bc, address);
        var (asker, riddle) = await pub.Connection<int>(Tag.PlayerA);                  Console.WriteLine($"Server received {riddle} from {asker}");
        // publishing without waiting does not work with single point for pending/delivered
        // it should be extracted out to the clients, or as a public state
        pub.Publish(Tag.Question, riddle);                                             Console.WriteLine("Server receives...");
        while (true) {
            var (solver, (m, n)) = await pub.Connection<(int, int)>(Tag.PlayerB);      Console.WriteLine($"Server received {m} {n} from {solver}");
            if (m * n == riddle) {
                //solver.Send(Tag.Accepted);
                asker.Send(Tag.Answer, (3, 5));                                        Console.WriteLine("Server done");
                break;
            } else {
                //solver.Send(Tag.Rejected);
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
    /// <summary>
    /// key 0 is for connection requests
    /// </summary>
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

    /// <summary>
    /// Query the pull of <paramref name="from"/> until a non-pending message to <paramref name="requestor"/> appears.
    /// </summary>
    /// <typeparam name="T">The expected type of the payload</typeparam>
    /// <param name="p">filter messages</param>
    /// <returns>The payload of the message and the address of the sender</returns>
    public async Task<(uint, T)> Receive<T>(Func<object, Metadata, T?> p) where T: struct {
        while (true) {
            lock (this) {
                foreach (var (payload, info) in publications) {
                    if (info.pending) {
                        var res = p(payload, info);
                        if (res != null) {
                            info.pending = false;
                            return (info.sender, (T)res);
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
class Link<E> {
    uint address;
    uint target;
    BC bc;

    public Link(BC bc, uint address, uint target) {
        this.address = address;
        this.target = target;
        this.bc = bc;
    }

    private (E, T)? f<T>(object payload, BC.Metadata info) {
        //Console.WriteLine(info.target == address);
        if (info.target != null && info.target != address)
            return null;
        try {
            return ((E, T))payload;
        } catch (InvalidCastException) {
            return null;
        }
    }

    public async Task<T> Receive<T>(E tag) {
        var (_, (_, v)) = await bc.Receive((payload, info) => {
            var res = f<T>(payload, info);
            if (res?.Item1.Equals(tag) == true)
                return res;
            return null;
        });
        return v;
    }

    public async Task SendAsync<T>(E tag, T payload) {
        await bc.PublishAsync((tag, payload), new BC.Metadata() { sender = address, target = target });
    }

    public Task SendAsync(E tag) {
        return SendAsync(tag, new Nothing());
    }

    public void Send<T>(E tag, T payload) {
        bc.Publish((tag, payload), new BC.Metadata() { sender = address, target = target });
    }

    public void Send(E tag) {
        Send(tag, new Nothing());
    }
}

class PublicLink<E> {
    uint address;
    BC bc;

    public PublicLink(BC bc, uint address) {
        this.address = address;
        this.bc = bc;
    }

    private (E, T)? f<T>(object payload, BC.Metadata info) {
        //Console.WriteLine(info.target == address);
        if (info.target != null && info.target != address)
            return null;
        try {
            return ((E, T))payload;
        } catch (InvalidCastException) {
            return null;
        }
    }

    public async Task<(Link<E>, T)> Connection<T>(E tag) {
        var (addr, (_, val)) = await bc.Receive((payload, info) => {
            var res = f<T>(payload, info);
            if (res?.Item1.Equals(tag) == true)
                return res;
            return null;
        });
        return (new Link<E>(bc, address, addr), val);
    }

    public void Publish<T>(E tag, T payload) {
        bc.Publish((tag, payload), new BC.Metadata() { sender = address, target = null });
    }
    public async Task PublishAsync<T>(E tag, T payload) {
        await bc.PublishAsync((tag, payload), new BC.Metadata() { sender = address, target = null });
    }
}
