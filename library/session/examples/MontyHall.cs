using System.Diagnostics;
using System.Threading.Tasks;
using static System.Console;
using static Utils;


static class MontyHall {
    public enum Door { a, b, c }

    struct H { }
    struct G { }

    private sealed class HCar : Args<int>, Dir<H, S> { internal HCar(int _1) { _ = _1; } }
    private sealed class Goat : Args<Door>, Dir<H, S>, Dir<S, G> { internal Goat(Door _1) { _ = _1; } }
    private sealed class Choice : Args<Door>, Dir<G, S>, Dir<S, H> { internal Choice(Door _1) { _ = _1; } }
    private sealed class Choice2 : Args<Door>, Dir<G, S> { internal Choice2(Door _1) { _ = _1; } }
    private sealed class Reveal : Dir<S, H> {  }
    private sealed class Car : Args<Hiding<Door>>, Dir<H, S> { internal Car(Hiding<Door> _1) { _ = _1; } }

    private interface Response : Dir<S, H>, Dir<S, G> { }
    private sealed class Winner : Response { }
    private sealed class Loser : Response { }

    static async Task Server(PublicLink @public) {
        (var host, int hiddenCar) = await @public.Connection<HCar, H>();
        (var guest, Door door1) = await @public.Connection<Choice, G>();

        host.Send(new Choice(door1));  Door goat = await host.Receive<Goat>();
        guest.Send(new Goat(goat));    Door door2 = await guest.Receive<Choice2>();
        host.Send(new Reveal());       Hiding<Door> hcar = await host.Receive<Car>();

        Door car = hcar.value;
        // FIX: confusing naming
        if (hcar.Hidden((uint)host.target) != hiddenCar || car == goat || car == door2) {
            guest.Send(new Winner());
            host.Send(new Loser());
        } else {
            guest.Send(new Loser()); 
            host.Send(new Winner());
        }
    }

    static async Task ClientHost(UpLink<H> server) {
        Door car = Door.a;
        var hcar = new Hiding<Door>(car, salt: 0x78573264);
        await server.SendAsync(new HCar(hcar.Hidden(server.address)));
        Door door1 = await server.ReceiveEarliest<Choice>();
        server.Send(new Goat(door1 == car ? Door.c : Door.b));
        await server.ReceiveEarliest<Reveal>();
        server.Send(new Car(hcar));
        switch (await server.ReceiveEarliest<Response>()) {
            case Winner x: WriteLine("Host won"); break;
            case Loser x: WriteLine("Host lost"); break;
            default: Debug.Assert(false); break;
        }
    }

    static async Task ClientGuest(UpLink<G> server) {
        await server.SendAsync(new Choice(Door.c));
        Door goat = await server.ReceiveEarliest<Goat>();
        Door door2 = goat == Door.b ? Door.a : Door.b;
        server.Send(new Choice2(door2));
        switch (await server.ReceiveEarliest<Response>()) {
            case Winner x: WriteLine("Guest won"); break;
            case Loser x: WriteLine("Guest lost"); break;
            default: Debug.Assert(false); break;
        }
    }

    internal static Task[] Players(BC bc) => new Task[] {
        Server(new PublicLink(bc, 0)),
        ClientHost(new UpLink<H>(bc, 1, 0)),
        ClientGuest(new UpLink<G>(bc, 2, 0))
    };
}
