using System;
using System.Collections.Generic;
using System.Linq;

struct Nothing { }

struct ConnectionRequest<Role> : Dir<S, Role> { }
struct ConnectionConfirmed<Role> : Dir<S, Role> { }

/// A blockchain event, possibly targeted at specific client. unlike packet, it's target
struct Mail { internal uint target; internal object payload; }
struct PublicMail { internal object payload; }

abstract class Link {
    public readonly uint address;
    public readonly BC bc;
    protected Link(BC bc, uint address) {
        this.address = address;
        this.bc = bc;
    }
}

abstract class PrivateLink : Link {
    public readonly uint target;
    protected PrivateLink(BC bc, uint address, uint target) : base(bc, address) {
        this.target = target;
    }
}

class PublicLink : Link {
    public PublicLink(BC bc, uint address) : base(bc, address) { }

    internal long Now() {
        return DateTime.Now.Ticks;
    }

    public Connector<T, Role> Connection<T, Role>() => new Connector<T, Role>() { link = this };
    public Connector<Nothing, Role> Connection<Role>() => Connection<Nothing, Role>();

    public void Publish<T>(T payload) where T : Dir<S, Client> {
        Console.WriteLine($"{address} publish {payload}");
        bc.events.Add(new PublicMail() { payload = payload });
    }
}

class ServerLink : Link {
    int lastLength = 1;
    public ServerLink(BC bc, uint address) : base(bc, address) {
        //bc.requests.Register(address);
    }

    public T ReceiveLatestPublic<T>() {
        // retrieves the newest message not seen yet
        while (true) {
            bc.Yield(address, $"Receive latest public {typeof(T)}");
            while (bc.events.Count == lastLength)
                bc.Yield(address, $"Waiting for events");
            var events = bc.events.Skip(lastLength).Reverse().ToList();
            lastLength = bc.events.Count;
            foreach (var e in events) {
                try {
                    return (T)((PublicMail)e).payload;
                } catch (InvalidCastException) {
                    //Console.WriteLine("Dropped");
                }
            }
            //Console.WriteLine("Nothing to read");
        }
    }

    public UpLink<Role> Connection<Role, T>(T payload) {
        bc.requests.SendRequest(address, (new ConnectionRequest<Role>(), payload));
        var res = new UpLink<Role>(bc, address, 0);
        res.ReceiveEarliest<ConnectionConfirmed<Role>>();
        return res;
    }
    public void Send<Role, T>(T payload) {
        bc.requests.SendRequest(address, (new ConnectionRequest<Role>(), payload));
    }
    public UpLink<Role> Connection<Role>() {
        return Connection<Role, Nothing>(new Nothing());
    }
}

class UpLink<Role> : PrivateLink {
    private int last = 0;

    public UpLink(BC bc, uint address, uint target) : base(bc, address, target) {
    }

    public T ReceiveEarliest<T>() where T : Dir<S, Role> {
        // retrieves the oldest message since the last one received
        // Console.WriteLine($"Client {address} receives");
        while (true) {
            bc.Yield(address, $"Receive earliest {typeof(T)}");
            for (; last < bc.events.Count; last++) {
                var payload = bc.events[last];
                try {
                    var mail = (Mail)payload;
                    if (mail.target == address) {
                        last++;
                        return (T)mail.payload;
                    } else {
                        //Console.WriteLine($"{address} dropped (wrong target) {payload}");
                    }
                } catch (InvalidCastException) {
                    //Console.WriteLine($"{address} dropped (wrong type) {payload} != {typeof(T)}");
                }
            }
        }
    }

    public void SendAsync<T>(T payload) where T : Dir<Role, S> {
        bc.requests.SendRequestAsync(address, payload);
    }
    public void SendAsync() {
        bc.requests.SendRequestAsync(address, new Nothing());
    }
    public void Send<T>(T payload) where T : Dir<Role, S> {
        bc.requests.SendRequest(address, payload);
    }
}

class DownLink<Role> : PrivateLink {
    public DownLink(BC bc, uint address, uint target) : base(bc, address, target) {
    }

    public Receiver<T> Receive<T>() where T : Dir<Role, S> => new Receiver<T>() { link=this };

    public void Send<T>(T payload) where T : Dir<S, Role> {
        bc.events.Add( new Mail() { target = target, payload=payload }) ;
    }
}

abstract class Acceptor<T, L> where L: Link {
    public L link;
    public abstract (bool, T) TryAccept(uint sender, object payload);

    public T Accept() {
        while (true) {
            var p = link.bc.requests.ReceiveRequest();
            var (ok, res) = TryAccept(p.sender, p.payload);
            if (!ok)
                continue;
            return res;
        }
    }
}

class Connector<T, Role> : Acceptor<(DownLink<Role>, T), PublicLink> {
    public override (bool, (DownLink<Role>, T)) TryAccept(uint sender, object payload) {
        var dlink = new DownLink<Role>(link.bc, link.address, sender);
        try {
            var (connok, res) = ((ConnectionRequest<Role>, T))payload;
            dlink.Send(new ConnectionConfirmed<Role>());
            return (true, (dlink, res));
        } catch (InvalidCastException) {
        }
        return (false, default);
    }
}

class Receiver<T> : Acceptor<T, PrivateLink> {
    public override (bool, T) TryAccept(uint sender, object payload) {
        try {
            if (sender == link.target) {
                return (true, (T)payload);
            }
        } catch (InvalidCastException) {
        }
        return (false, default);
    }
}


static class Combinators {
    public static (T1, T2) Parallel<T1, L1, T2, L2>(Acceptor<T1, L1> t1, Acceptor<T2, L2> t2) where L1: Link where L2: Link {
        BC bc = t1.link.bc;
        T1 left = default;        bool doneLeft = false;
        T2 right = default;       bool doneRight = false;
        while (!doneLeft || !doneRight) {
            var p = bc.requests.ReceiveRequest();
            var (ok1, p1) = t1.TryAccept(p.sender, p.payload);
            var (ok2, p2) = t2.TryAccept(p.sender, p.payload);
            if (ok1 && !doneLeft) {
                left = p1;
                doneLeft = true;
            } else if (ok2 && !doneRight) {
                right = p2;
                doneRight = true;
            } else {
                Console.WriteLine("Dropped packets");
            }
        }
        return (left, right);
    }

    public static T[] ParallelMany<T, L>(Acceptor<T, L> t) where L : Link {
        throw new NotImplementedException();
    }
}
