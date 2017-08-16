using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using System.Threading.Tasks.Schedulers;


class Playground {
    enum Tag {
        PlayerA, PlayerB, Question, Answer
    }

    static async Task ClientQuestion(uint address) {
        var link = new UpLink(bc, address, serverAddress);          Console.WriteLine($"Client {address} sends question");
        await link.Send(Tag.PlayerA, 15);
        var (m, n) = await link.Receive<(int, int)>(Tag.Answer);    Console.WriteLine($"Client {address} received solution ({m}, {n})");
    }

    static async Task ClientAnswer(uint address) {
        var link = new UpLink(bc, address, serverAddress);      Console.WriteLine($"Client {address} fetches question");
        var riddle = await link.Receive<int>(Tag.Question);     Console.WriteLine($"Client {address} sends solution {(3, 5)}");
        // pretend we are solving the problem
        await link.Send(Tag.PlayerB, (3, 5));                   Console.WriteLine($"Client {address} done");
    }

    static async Task Server(uint address) {
        var (asker, riddle) = await bc.Receive<int>(Tag.PlayerA, address);  Console.WriteLine($"Server received {riddle} from {asker}");
        // publishing without waiting does not work with single point for pending/delivered
        // it should be extracted out to the clients, or as a public state
        bc.Publish(riddle, new Metadata() { tag = Tag.Question, sender = address, target = null });     Console.WriteLine("Server receives...");
        var (solver, (m, n)) = await bc.Receive<(int, int)>(Tag.PlayerB, address);                      Console.WriteLine($"Server received {m} {n} from {solver}");
        await bc.PublishAsync((3, 5), new Metadata() { tag = Tag.Answer, sender = address, target = asker });   Console.WriteLine("Server done");
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

public class Metadata {
    public uint sender;
    // null means everyone
    public uint? target;
    public object tag;
    public volatile bool pending = true;
    public override string ToString() => $"{sender} -> {target} ({pending})";
}

class BC {
    /// <summary>
    /// key 0 is for connection requests
    /// </summary>
    Dictionary<uint, List<(object, Metadata)>> publications = new Dictionary<uint, List<(object, Metadata)>>();

    public BC(params uint[] addresses) {
        foreach (var address in addresses)
            publications[address] = new List<(object, Metadata)> {  };
    }

    public void Publish(object payload, Metadata info) {
        lock (this) {
            publications[info.sender].Add((payload, info));
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
    /// <param name="requestor">Receiver of the message</param>
    /// <param name="from">Expected senders of the message</param>
    /// <returns>The payload of the message</returns>
    public async Task<(uint, T)> Receive<T>(object tag, uint requestor, params uint[] froms) {
        while (true) {
            if (froms.Length == 0)
                froms = publications.Keys.ToArray();
            lock (this) {
                foreach (var from in froms) {
                    var v = publications[from];
                    foreach (var (payload, info) in v) {
                        if (info.pending
                            && (info.tag.Equals(tag))
                            && (info.target == null || info.target == requestor)
                            && typeof(T).IsInstanceOfType(payload)) {
                            info.pending = false;
                            return (info.sender, (T)payload);
                        }
                    }
                }
            }
            await Task.Yield();
        }
    }
}

/// <summary>
///  Helper class, hides some ugly parameters
/// </summary>
class UpLink {
    uint address;
    uint target;
    BC bc;

    public UpLink(BC bc, uint address, uint target) {
        this.address = address;
        this.target = target;
        this.bc = bc;
    }
    public async Task<T> Receive<T>(object tag) {
        var (_, v) = await bc.Receive<T>(tag, address, new uint[] { target });
        return v;
    }
    public async Task Send<T>(object tag, T payload) {
        await bc.PublishAsync(payload, new Metadata() { tag = tag, sender = address, target = target });
    }
}