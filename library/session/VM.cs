using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using System.Threading.Tasks.Schedulers;

interface IConnectionRequest { }
struct A: IConnectionRequest { }
struct B: IConnectionRequest { }

class Playground {
    static BC bc;
    const uint serverAddress = 1;

    static async Task ClientQuestion(uint address) {
        Console.WriteLine($"Client {address} sends");
        await bc.PublishAsync((default(A), 15), new Metadata() { sender = address, target = serverAddress });
        var (solver, (m, n)) = await bc.Receive<(int, int)>(address, serverAddress);
        Console.WriteLine($"Client {address} received solution {m}, {n}");
    }

    static async Task ClientAnswer(uint address) {
        Console.WriteLine($"Client {address} sends");
        await bc.PublishAsync((default(B), (3, 5)), new Metadata() { sender = address, target = serverAddress });
        Console.WriteLine($"Client {address} done");
    }

    static async Task Server(uint address) {
        var (asker, (_, riddle)) = await bc.Receive<(A, int)>(address);
        Console.WriteLine($"Server received {riddle} from {asker}");
        // publishing without waiting does not work with single point for pending/delivered
        // it should be extracted out to the clients, or as a public state
        //bc.Publish(riddle, new Metadata() { sender = address, target = null });
        Console.WriteLine("Server receives...");
        var (solver, (_, (m, n))) = await bc.Receive<(B, (int, int))>(address);
        Console.WriteLine($"Server received {m} {n} from {solver}");
        await bc.PublishAsync((3, 5), new Metadata() { sender = address, target = asker });
        Console.WriteLine($"Server done");
    }

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
    // {} means everyone
    public uint? target;
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
            publications[address] = new List<(object, Metadata)> { (null, new Metadata() { pending = false }) };
    }

    public async Task PublishAsync<T>(T payload, Metadata info) {
        lock (this) {
            publications[info.sender].Add((payload, info));
        }

        while (!info.pending) {
            //Console.WriteLine($"Sender {msg.sender} yields");
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
    public async Task<(uint, T)> Receive<T>(uint requestor, params uint[] froms) {
        while (true) {
            if (froms.Length == 0)
                froms = publications.Keys.ToArray();
            lock (this) {
                foreach (var from in froms) {
                    var v = publications[from];
                    foreach (var (payload, info) in v) {
                        if (info.pending && info.target == requestor
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
