using System;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

struct Nothing { }

struct ConnectionRequest<Role> : Dir<S, Role> { }
struct ConnectionConfirmed<Role> : Dir<S, Role> { }

/// A blockchain event, possibly targeted at specific client. unlike packet, it's target
struct Mail<T> { internal uint target; internal T payload; }
struct PublicMail<T> { internal T payload; }

abstract class Link {
    public readonly uint address;
    public readonly uint? target;
    public readonly BC bc;
    protected Link(uint address, uint? target, BC bc) {
        this.address = address;
        this.target = target;
        this.bc = bc;
    }
}

class PublicLink : Link {
    public PublicLink(BC bc, uint address) : base(address, null, bc) { }
    public Connector<T, Role> Connection<T, Role>() => new Connector<T, Role>() { link = this };
    public Connector<Nothing, Role> Connection<Role>() => Connection<Nothing, Role>();

    public void Publish<T>(T payload) where T : Dir<S, Client> {
        bc.events.Add(new PublicMail<T>() { payload = payload });
    }
}

class ServerLink: Link {
    public ServerLink(BC bc, uint address) : base(address, null, bc) {
        //bc.requests.Register(address);
    }

    public async Task<T> ReceiveLatestPublic<T>() {
        // retrieves the newest message
        while (true) {
            bc.Yield(address, $"Receive latest public {typeof(T)}");
            try {
                var mail = (PublicMail<T>)bc.events.FindLast(x => {
                    return typeof(PublicMail<T>).IsAssignableFrom(x.GetType());
                });
                return mail.payload;
            } catch (InvalidCastException) {
                Console.WriteLine("Dropped");
            }
            Console.WriteLine("Nothing to read");
        }
    }

    public async Task<UpLink<Role>> Connection<Role, T>(T payload) {
        bc.requests.SendRequest(address, (new ConnectionRequest<Role>(), payload));
        var res = new UpLink<Role>(bc, address, 0);
        await res.ReceiveEarliest<ConnectionConfirmed<Role>>();
        return res;
    }

    public async Task<UpLink<Role>> Connection<Role>() {
        return await Connection<Role, Nothing>(new Nothing());
    }
}

class UpLink<Role> : Link {
    private int last = 0;

    public UpLink(BC bc, uint address, uint target) : base(address, target, bc) {
    }

    public async Task<T> ReceiveEarliest<T>() where T : Dir<S, Role> {
        // retrieves the oldest message since the last one received
        // Console.WriteLine($"Client {address} receives");
        while (true) {
            bc.Yield(address, $"Receive earliest {typeof(T)}");
            for (; last < bc.events.Count; last++) {
                try {
                    var mail = (Mail<T>)bc.events[last];
                    if (mail.target == address) {
                        last++;
                        return mail.payload;
                    } else {
                    }
                } catch (InvalidCastException) {
                }
            }
        }
    }

    public async Task SendAsync<T>(T payload) where T : Dir<Role, S> {
        await bc.requests.SendRequestAsync(address, payload);
    }
    public async Task SendAsync() {
        await bc.requests.SendRequestAsync(address, new Nothing());
    }
    public void Send<T>(T payload) where T : Dir<Role, S> {
        bc.requests.SendRequest(address, payload);
    }
}

class DownLink<Role> : Link {
    public DownLink(BC bc, uint address, uint target) : base(address, target, bc) {
    }

    public Receiver<T> Receive<T>() where T : Dir<Role, S> => new Receiver<T>() { link=this };

    public void Send<T>(T payload) where T : Dir<S, Role> {
        bc.events.Add( new Mail<T>() { target = (uint)target, payload=payload }) ;
    }
}

abstract class Acceptor<T> {
    public Link link;
    public abstract (bool, T) TryAccept(uint sender, object payload);

    private async Task<T> Accept() {
        while (true) {
            var p = await link.bc.requests.ReceiveRequest();
            var (ok, res) = TryAccept(p.sender, p.payload);
            if (!ok)
                continue;
            return res;
        }
    }

    public System.Runtime.CompilerServices.TaskAwaiter<T> GetAwaiter() {
        return Accept().GetAwaiter();
    }

}

class Connector<T, Role> : Acceptor<(DownLink<Role>, T)> {
    public override (bool, (DownLink<Role>, T)) TryAccept(uint sender, object payload) {
        try {
            var (connok, res) = ((ConnectionRequest<Role>, T))payload;
            var dlink = new DownLink<Role>(link.bc, link.address, sender);
            dlink.Send(new ConnectionConfirmed<Role>());
            return (true, (dlink, res));
        } catch (InvalidCastException) {
        }
        return (false, default);
    }
}

class Receiver<T> : Acceptor<T> {
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
    public static async Task<(T1, T2)> Parallel<T1, T2>(Acceptor<T1> t1, Acceptor<T2> t2) {
        BC bc = t1.link.bc;
        T1 left = default;        bool doneLeft = false;
        T2 right = default;       bool doneRight = false;
        while (!doneLeft || !doneRight) {
            var p = await bc.requests.ReceiveRequest();
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
}
