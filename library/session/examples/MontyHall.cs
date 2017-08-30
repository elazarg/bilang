using System;
using System.Diagnostics;
using static System.Console;
using static Utils;

namespace MontyHall {
    /*
        global protocol MontyHall(role S, role P, role H, role G) {
            hiddenCar(int) from H to S;
            hiddenCar() from S to G;

            door1(int) from G to S;
            door1(int) from S to H;

            goat(int) from H to S;
            goat(int) from S to G;

            door2(int) from G to S;
            door2(int) from S to H;

            openCar(int) from H to S;
            choice at S {
                won() from S to G;
                lost() from S to H;
            } or {
                won() from S to H;
                lost() from S to G;
            }
        }
    */
    static class MontyHall {
        static void Server(PublicLink @public) {
            var ((host, _), (guest, _)) = Combinators.Parallel(@public.Connection<H>(), @public.Connection<G>());

            int hiddenCar = host.Receive<HCar>().Accept();
            guest.Send(new HCar(hiddenCar));

            Door door1 = guest.Receive<Choice1>().Accept();
            host.Send(new Choice1(door1));

            Door goat = host.Receive<Goat>().Accept();
            guest.Send(new Goat(goat));

            Door door2 = guest.Receive<Choice2>().Accept();
            host.Send(new Reveal());
            Hiding<Door> hcar = host.Receive<Car>().Accept();

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

        static void ClientHost(ServerLink server) {
            var c = server.Connection<H>();
            Door car = Door.a;
            var hcar = new Hiding<Door>(car, salt: 0x78573264);
            c.Send(new HCar(hcar.Hidden(server.address)));

            Door door1 = c.ReceiveEarliest<Choice1>();
            c.Send(new Goat(door1 == car ? Door.c : Door.b));
            c.ReceiveEarliest<Reveal>();
            c.Send(new Car(hcar));
            switch (c.ReceiveEarliest<IResponse>()) {
                case Winner x: WriteLine("Host won"); break;
                case Loser x: WriteLine("Host lost"); break;
                default: Debug.Assert(false); break;
            }
        }

        static void ClientGuest(ServerLink server) {
            var c = server.Connection<G>();
            c.ReceiveEarliest<HCar>();
            c.Send(new Choice1(Door.c));
            Door goat = c.ReceiveEarliest<Goat>();
            Door door2 = goat == Door.b ? Door.a : Door.b;
            c.Send(new Choice2(door2));
            switch (c.ReceiveEarliest<IResponse>()) {
                case Winner x: WriteLine("Guest won"); break;
                case Loser x: WriteLine("Guest lost"); break;
                default: Debug.Assert(false); break;
            }
        }

        internal static Session Players = new Session(Server, ClientHost, ClientGuest);
    }

    public enum Door { a, b, c }

    struct H : Dir<S, Client> { }
    struct G : Dir<S, Client> { }

    sealed class HCar : Args<int>, Dir<H, S>, Dir<S, G> { internal HCar(int _1) { _ = _1; } }
    sealed class Goat : Args<Door>, Dir<H, S>, Dir<S, G> { internal Goat(Door _1) { _ = _1; } }
    sealed class Choice1 : Args<Door>, Dir<G, S>, Dir<S, H> { internal Choice1(Door _1) { _ = _1; } }
    sealed class Choice2 : Args<Door>, Dir<G, S> { internal Choice2(Door _1) { _ = _1; } }
    sealed class Reveal : Dir<S, H> { }
    sealed class Car : Args<Hiding<Door>>, Dir<H, S> { internal Car(Hiding<Door> _1) { _ = _1; } }

    interface IResponse : Dir<S, H>, Dir<S, G> { }
    sealed class Winner : IResponse { }
    sealed class Loser : IResponse { }

}

/*
    global protocol MontyHall(role S, role P, role H, role G) {
        hiddenCar(int) from H to G;
        door1(int) from G to H;
        goat(int) from H to G;
        door2(int) from G to H;
        openCar(int) from H to G;
        choice at (H+G) {
            youWon() from H to G;
        } or {
            youWon() from G to H;
        }
    }
*/
