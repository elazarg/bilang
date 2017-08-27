using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using System.Threading.Tasks.Dataflow;
using System.Linq;
using System.Threading;


class BC {
    internal readonly uint serverAddress = 0;
    internal readonly Requests requests;
    public BC() {
        requests = new Requests() { bc = this };
    }

    internal readonly List<object> events = new List<object>();

    object[] d = new object[5];

    private void Prompt(string s) {
        Console.Write($"\r{s}\n>>> ");
        Console.Out.Flush();
    }

    public void Yield(uint address, object details) {
        Prompt($"Waiting - {address}: {details}");
        Monitor.Wait(d[address]);
        Prompt($"Running {address}");
    }
    
    public void Start(params Action[] ts) {
        TaskFactory factory = new TaskFactory();
        uint i = 0;
        foreach (var t in ts) {
            var val = new object();
            requests.Register(i);
            d[i] = val;
            new Thread(() => { Monitor.Enter(val); t(); }).Start();
            i++;
        }
        while (true) {
            var s = Console.ReadLine();
            if (s == "exit")
                return;
            if (uint.TryParse(s, out uint num)) {
                Console.WriteLine($"Take lock {num}");
                lock (d[num]) {
                    Console.WriteLine("send pulse");
                    Monitor.Pulse(d[num]);
                    Console.WriteLine("sent");
                }
            }
        }
    }
}

struct Packet {
    internal uint sender;
    internal object payload;
    public void Deconstruct(out uint _1, out object _2) {
        _1 = sender; _2 = payload;
    }
    public override string ToString() {
        return $"Packet({sender}: {payload})";
    }
}

class Requests {
    public BC bc;
    private Dictionary<uint, ITargetBlock<object>> requests = new Dictionary<uint, ITargetBlock<object>>();

    private BufferBlock<Packet> server = new BufferBlock<Packet>();

    public void Register(uint sender) {
        var block = new BufferBlock<object>();
        requests[sender] = block;
        // TODO: make sure we still have all possible races
        var t = new TransformBlock<object, Packet>(payload => new Packet() { sender = sender, payload = payload });
        block.LinkTo(t);
        t.LinkTo(server);
    }

    public void SendRequest(uint sender, object payload) {
        requests[sender].Post(payload);
        bc.Yield(sender, $"Sent {payload}");
    }

    public async Task<bool> SendRequestAsync(uint sender, object payload) {
        var res = await requests[sender].SendAsync(payload);
        bc.Yield(sender, $"Sending {payload}");
        return res;
    }

    public async Task<Packet> ReceiveRequest() {
        // this is an actual "method call" execution
        bc.Yield(0, $"Receiving");
        return await server.ReceiveAsync();
    }
}
