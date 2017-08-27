using System;
using System.Collections.Generic;
using System.Threading.Tasks.Dataflow;
using System.Threading;


class BC {
    internal readonly uint serverAddress = 0;
    internal readonly Requests requests;
    public BC() {
        requests = new Requests() { bc = this };
    }

    internal readonly List<object> events = new List<object>();

    BufferBlock<bool>[] run = new BufferBlock<bool>[5];

    private void Prompt(string s) {
        Console.Write($"\r{s}\n>>> ");
        Console.Out.Flush();
    }

    public void Yield(uint address, object details) {
        Prompt($"Waiting - {address}: {details}");
        run[address].Receive();
        Prompt($"Running {address}");
    }
    
    public void Start(params Action[] ts) {
        uint i = 0;
        foreach (var t in ts) {
            var val = new object();
            requests.Register(i);
            run[i] = new BufferBlock<bool>();
            new Thread(() => t()).Start();
            i++;
        }
        while (true) {
            var s = Console.ReadLine();
            if (s == "exit")
                return;
            if (uint.TryParse(s, out uint address)) {
                Console.WriteLine($"Wake {address}");
                run[address].Post(true);
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

    public bool SendRequestAsync(uint sender, object payload) {
        var res = requests[sender].Post(payload);
        bc.Yield(sender, $"Sending {payload}");
        return res;
    }

    public Packet ReceiveRequest() {
        // this is an actual "method call" execution
        bc.Yield(0, $"Receiving");
        return server.Receive();
    }
}
