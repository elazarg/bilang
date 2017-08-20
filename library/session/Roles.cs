using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;


interface Dir<out From, in To> { } // "in" since we want to be covariant
interface Client { }

abstract class Args<T> {
    internal T _;
    public static implicit operator T(Args<T> a) { return a._; }
    public override string ToString() { return $"{GetType()}{_}"; }
}

static class ExtD {
    internal static void Deconstruct<T>(this Args<T> d, out T res) { res = d._; }
    internal static void Deconstruct<T1, T2>(this Args<(T1, T2)> d, out T1 res1, out T2 res2) { (res1, res2) = d._; }
    internal static void Deconstruct<T1, T2, T3>(this Args<(T1, T2, T3)> d, out T1 res1, out T2 res2, out T3 res3) { (res1, res2, res3) = d._; }
}

struct Nothing { }

/// <summary>
///  Helper class: one side of a binary channel, hides some ugly parameters
/// </summary>
abstract class Link {
    protected BC bc;
    public uint address;

    public Link(BC bc, uint address) {
        this.address = address;
        this.bc = bc;
    }

    protected (bool, T) f<T>(object payload, BC.Metadata info) {
        if (info.target != null && info.target != address)
            return (false, default);
        try {
            return (true, (T)payload);
        } catch (InvalidCastException) {
            return (false, default);
        }
    }
}

class DirLink<From, To> : Link {
    public readonly uint target;

    public DirLink(BC bc, uint address, uint target) : base(bc, address) {
        this.target = target;
    }

    public async Task<T> Receive<T>() where T : Dir<To, From> {
        (uint _, T v) = await bc.Receive(f<T>);
        return v;
    }

    public async Task SendAsync<T>(T payload) where T : Dir<From, To> {
        await bc.PublishAsync(payload, new BC.Metadata() { sender = address, target = target });
    }
    public async Task SendAsync() {
        await bc.PublishAsync(new Nothing(), new BC.Metadata() { sender = address, target = target });
    }
    public void Send<T>(T payload) where T : Dir<From, To> {
        bc.Publish(payload, new BC.Metadata() { sender = address, target = target });
    }
}

class PublicLink<From> : Link {
    public PublicLink(BC bc, uint address) : base(bc, address) {
    }

    public async Task<(DirLink<From, To>, T)> Connection<T, To>() {
        (uint addr, T val) = await bc.Receive(f<T>);
        return (new DirLink<From, To>(bc, address, addr), val);
    }
    public async Task<DirLink<From, To>> Connection<To>() {
        return (await Connection<Nothing, To>()).Item1;
    }

    public void Publish<T>(T payload) where T : Dir<From, Client> {
        bc.Publish(payload, new BC.Metadata() { sender = address, target = null });
    }
    public async Task PublishAsync<T>(T payload) where T : Dir<From, Client> {
        await bc.PublishAsync(payload, new BC.Metadata() { sender = address, target = null });
    }
}

static class Combinators {
    public static async Task<(T1, T2)> Parallel<T1, T2>(Task<T1> t1, Task<T2> t2) {
        System.Threading.Tasks.Parallel.Invoke(async () => await t1, async () => await t2);
        return (t1.Result, t2.Result);
    }
}