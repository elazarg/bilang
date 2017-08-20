using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using System.Threading.Tasks.Schedulers;

class BC {
    public class Metadata {
        public uint sender;
        // null means everyone
        public uint? target;
        public volatile bool pending = true;
        public override string ToString() => $"{sender} -> {target} ({pending})";
    }
    OrderedTaskScheduler scheduler = new OrderedTaskScheduler();

    public void Start(params Task[] ts) {
        TaskFactory factory = new TaskFactory(scheduler);
        foreach (var t in ts)
            factory.StartNew(t.RunSynchronously);
    }

    List<(object, Metadata)> publications = new List<(object, Metadata)>();

    public void Publish(object payload, Metadata info) {
        lock (this) {
            publications.Add((payload, info));
        }
    }

    public async Task PublishAsync(object payload, Metadata info) {
        Publish(payload, info);
        while (info.pending) {
            await scheduler.Yield();
        }
    }
    
    public async Task<(uint, T)> Receive<T>(Func<object, Metadata, (bool, T)> p) {
        while (true) {
            lock (this) {
                foreach (var (payload, info) in publications) {
                    if (info.pending) {
                        var (ok, res) = p(payload, info);
                        if (ok) {
                            info.pending = false;
                            return (info.sender, res);
                        }
                    }
                }
            }
            await scheduler.Yield();
        }
    }
}
