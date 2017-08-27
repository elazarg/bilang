using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using System.Threading.Tasks.Dataflow;
using System.Threading.Tasks.Schedulers;
using System.Linq;

class BC {
    internal readonly uint serverAddress = 0;
    internal readonly Requests requests = new Requests();

    internal readonly List<object> events = new List<object>();

    readonly OrderedTaskScheduler scheduler = new OrderedTaskScheduler();
    public void Start(params Task[] ts) {
        TaskFactory factory = new TaskFactory();
        foreach (var t in ts)
            factory.StartNew(t.RunSynchronously);
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
        //Console.WriteLine($"Client {sender} posts {payload}");
        requests[sender].Post(payload);
    }

    public async Task<bool> SendRequestAsync(uint sender, object payload) {
        //Console.WriteLine($"Client {sender} sends {payload}");
        return await requests[sender].SendAsync(payload);
    }

    public async Task<Packet> ReceiveRequest() {
        // this is an actual "method call" execution
        return await server.ReceiveAsync();
    }
}
