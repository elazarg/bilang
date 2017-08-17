using System;
using System.Diagnostics;
using System.Threading.Tasks;
using static System.Console;
using static Utils;


static class MontyHallNew {
    public enum Door { a, b, c }

    interface H { }
    interface G { }
    interface S { }

    private sealed class HDoor : Args<int>, Dir<H, S> { internal HDoor(int _1) { _ = _1; } }
    private sealed class Goat : Args<Door>, Dir<H, S>, Dir<S, G> { internal Goat(Door _1) { _ = _1; } }
    private sealed class Choice : Args<Door>, Dir<G, S>, Dir<S, H> { internal Choice(Door _1) { _ = _1; } }
    private sealed class Choice2 : Args<Door>, Dir<G, S> { internal Choice2(Door _1) { _ = _1; } }
    private sealed class Reveal : Dir<S, H> {  }
    private sealed class Car : Args<Hiding<Door>>, Dir<H, S> { internal Car(Hiding<Door> _1) { _ = _1; } }

    private interface Response : Dir<S, H>, Dir<S, G> { }
    private sealed class Winner : Response { }
    private sealed class Loser : Response { }

    static async Task Server(PublicLink<S> pub) {
        (var host, int hiddenCar) = await pub.Connection<HDoor, H>();
        (var guest, Door door1) = await pub.Connection<Choice, G>();
        host.Send(new Choice(door1));
        Door goat = await host.Receive<Goat>();
        guest.Send(new Goat(goat));
        Door door2 = await guest.Receive<Choice2>();
        host.Send(new Reveal());
        Hiding<Door> hcar = await host.Receive<Car>();
        Door car = hcar.value;
        // FIX: confusing naming
        if (hcar.Hidden(host.target) != hiddenCar || car == goat || car == door2) {
            guest.Send(new Winner());
            host.Send(new Loser());
        } else {
            guest.Send(new Loser()); 
            host.Send(new Winner());
        }
    }

    static async Task ClientHost(DirLink<H, S> link) {
        Door car = Door.a;
        var hcar = new Hiding<Door>(car, 0x78573264);
        await link.SendAsync(new HDoor(hcar.Hidden(link.address)));
        Door door1 = await link.Receive<Choice>();
        link.Send(new Goat(door1 == car ? Door.c : Door.b));
        await link.Receive<Reveal>();
        link.Send(new Car(hcar));
        switch (await link.Receive<Response>()) {
            case Winner x: WriteLine("Host won"); break;
            case Loser x: WriteLine("Host lost"); break;
            default: Debug.Assert(false); break;
        }
    }

    static async Task ClientGuest(DirLink<G, S> link) {
        await link.SendAsync(new Choice(Door.c));
        Door goat = await link.Receive<Goat>();
        Door door2 = goat == Door.b ? Door.a : Door.b;
        link.Send(new Choice2(door2));
        switch (await link.Receive<Response>()) {
            case Winner x: WriteLine("Guest won"); break;
            case Loser x: WriteLine("Guest lost"); break;
            default: Debug.Assert(false); break;
        }
    }

    internal static Task[] Players(BC bc) => new Task[] {
        Server(new PublicLink<S>(bc, 0)),
        ClientHost(new DirLink<H, S>(bc, 1, 0)),
        ClientGuest(new DirLink<G, S>(bc, 2, 0))
    };
}
