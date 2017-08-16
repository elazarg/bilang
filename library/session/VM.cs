using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using System.Threading.Tasks.Schedulers;


class Playground {
    static BC bc;

    static async Task Client(uint address, string payload) {
        Console.WriteLine($"Client {address} sends");
        await bc.PublishAsync(payload, new Metadata() { sender = address, desired_target = 1 });
    }

    static async Task Server(uint address) {
        Console.WriteLine("Server receives...");
        Console.WriteLine("Server received " + await bc.Receive<string>(address, 2));
        Console.WriteLine("Server received " + await bc.Receive<string>(address, 3));
    }

    static TaskFactory factory = new TaskFactory(new OrderedTaskScheduler());

    public static void Start(Task t) {
        factory.StartNew(t.RunSynchronously);
    }

    public static void Main() {
        bc = new BC(1, 2, 3);
        Start(Server(1));
        Start(Client(2, "Alice"));
        Start(Client(3, "Bob"));

        Console.ReadKey();
    }
}

public class Metadata {
    public uint sender;
    public uint? desired_target;
    public volatile bool pending = true;
    public override string ToString() => $"{sender} -> {desired_target} ({pending})";
}

class BC {
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
    /// Query the pull of <paramref name="from"/> until a non-pending message to <paramref name="requestor"/> appears
    /// </summary>
    /// <typeparam name="T">The expected type of the payload</typeparam>
    /// <param name="requestor">Receiver of the message</param>
    /// <param name="from">Expected sender of the message</param>
    /// <returns>The payload of the message</returns>
    public async Task<T> Receive<T>(uint requestor, uint from) {
        while (true) {
            lock (this) {
                var v = publications[from];
                foreach (var (payload, info) in v) {
                    if (info.pending && info.desired_target == requestor
                        && typeof(T).IsInstanceOfType(payload)) {
                        info.pending = false;
                        return (T)payload;
                    }
                }
            }
            //Console.WriteLine($"Requestor {requestor} yields");
            await Task.Yield();
        }
    }
}
