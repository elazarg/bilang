using System;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;
using System.Threading.Tasks.Dataflow;
using System.Threading.Tasks.Schedulers;

class BC {
    internal readonly Requests requests = new Requests();
    internal readonly Events events = new Events();
    readonly OrderedTaskScheduler scheduler = new OrderedTaskScheduler();

    public void Start(params Task[] ts) {
        TaskFactory factory = new TaskFactory(scheduler);
        foreach (var t in ts)
            factory.StartNew(t.RunSynchronously);
    }
}

class Requests {
    Dictionary<uint, ITargetBlock<object>> requests = new Dictionary<uint, ITargetBlock<object>>();

    // for simplicity we ignore the target since there's only one for now
    ISourceBlock<object> server = new BufferBlock<object>();

    void Register(uint sender) {
        var block = new BufferBlock<object>();
        requests[sender] = block;
        // TODO: make sure we still have all possible races
        block.LinkTo((BufferBlock<object>)server);
    }

    public void SendRequest(object payload, uint sender, uint target) {
        requests[sender].Post(payload);
    }

    public async Task<bool> SendRequestAsync(object payload, uint sender, uint target) {
        return await requests[sender].SendAsync(payload);
    }

    public async Task<object> ReceiveRequest<T>(Func<object> p, uint target) {
        return await server.ReceiveAsync();
    }
}

class Events {
    List<(object, uint)> events = new List<(object, uint)>();

    public void PublishEvent(object payload, uint sender) {
        lock (this) {
            events.Add((payload, sender));
        }
    }

    public async Task<(uint, T)> ReadEvents<T>(Func<object, uint, (bool, T)> p) {
        while (true) {
            lock (this) {
                // this reverse might break things
                for (int i = events.Count - 1; i >= 0; i++) {
                    var (payload, sender) = events[i];
                    var (ok, res) = p(payload, sender);
                    if (ok) {
                        return (sender, res);
                    }
                }
            }
            await Task.Yield();
        }
    }
}