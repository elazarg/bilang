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

    BufferBlock<bool>[] run;
    BroadcastBlock<string>[] state;

    private void Prompt(string s) {
        Console.Write($"\r{s}\n>>> ");
        Console.Out.Flush();
    }

    public void Yield(uint address, object details) {
        state[address].Post($"Waiting: {details}");
        run[address].Receive();
        state[address].Post($"Running");
    }
    
    public void Start(params Action[] ts) {
        var threads = new List<Thread>();
        int n = ts.Length;
        run = new BufferBlock<bool>[n];
        state = new BroadcastBlock<string>[n];
        for (uint i = 0; i < n; i++) {
            var val = new object();
            requests.Register(i);
            run[i] = new BufferBlock<bool>();
            state[i] = new BroadcastBlock<string>(x=>x);
            state[i].Post("Nothing");
            var t = ts[i];
            threads.Add(new Thread(() => t()));
        }
        foreach (var t in threads)
            t.Start();
        Prompt("Start game");
        while (true) {
            var s = Console.ReadLine();
            if (s == "exit" || s == "q" || s == "quit") {
                Console.WriteLine("Killing threads");
                foreach (var t in threads)
                    t.Abort();
                Console.WriteLine("Exiting");
                return;
            } else if (uint.TryParse(s, out uint address)) {
                if (address < n) {
                    Prompt($"Wake {address}");
                    run[address].Post(true);
                } else {
                    Prompt($"Bad address {address}");
                }
            } else if (s != "") {
                Prompt($"Unkown command {s}");
            } else {
                address = (uint)new Random().Next();
                Prompt($"Wake {address % n}");
                run[address % n].Post(true);
            }
            {
                for (uint i = 0; i < n; i++) {
                    var v = state[i].Receive();
                    Prompt($"{i}: {v}");
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

    public bool SendRequestAsync(uint sender, object payload) {
        var res = requests[sender].Post(payload);
        bc.Yield(sender, $"Sending {payload}");
        return res;
    }

    public Packet ReceiveRequest() {
        // this is an actual "method call" execution
        bc.Yield(0, $"Receiving");
        var res =  server.Receive();
        bc.Yield(0, $"Received");
        return res;
    }
}
