using System;
using System.Collections.Generic;
using System.Threading.Tasks.Dataflow;
using System.Threading;

class BC {
    internal readonly Requests requests;
    internal readonly List<object> events = new List<object>() { "Header" };
    readonly Controller controller;

    public BC(Controller c) {
        controller = c;
        requests = new Requests() { bc = this };
    }

    public void Yield(uint address, object details) {
        controller.Yield(address, details);
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
