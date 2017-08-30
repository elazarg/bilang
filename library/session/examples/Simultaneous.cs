using System;
using System.Diagnostics;
using static System.Console;
using static Combinators;
using static Utils;

namespace Simultaneous {
    /*
        global protocol Simultaneous(role S, role E, role O) {
            par {
                hiddenChoice(int) from E to S;
            } and {
                hiddenChoice(int) from E to S;
            }

            reveal() from S to E;
            reveal() from S to O;

            par {
                choice(Hiding[bool]) from E to S;
            } and {
                choice(Hiding[bool]) from E to S;
            }
            choice at S {
                won() from S to E;
                lost() from S to O;
            } or {
                won() from S to O;
                lost() from S to E;
            }
        }
    */
    static class Simultaneous {
        static void Server(PublicLink @public) {
            var ((even, even_hchoice), (odd, odd_hchoice)) = Parallel(
                @public.Connection<HChoice, E>(),
                @public.Connection<HChoice, O>()
            );
            even.Send(new Reveal());
            odd.Send(new Reveal());
            (Hiding<bool> even_choice, Hiding<bool> odd_choice) = Parallel(
                even.Receive<Choice>(),
                odd.Receive<Choice>()
            );
            bool even_honest = even_choice.Hidden(even.target) == even_hchoice;
            bool odd_honest = odd_choice.Hidden(odd.target) == odd_hchoice;
            if (!even_honest && !odd_honest) {
                even.Send(new Lost());
                odd.Send(new Lost());
            } else if (!odd_honest || even_choice.value == odd_choice.value) {
                even.Send(new Won());
                odd.Send(new Lost());
            } else {
                even.Send(new Lost());
                odd.Send(new Won());
            }
        }

        static void ClientEven(ServerLink server) {
            bool choice = true;
            var hchoice = new Hiding<bool>(choice, salt: 0x78573264);
            var c = server.Connection<E, HChoice>(new HChoice(hchoice.Hidden(server.address)));
            c.ReceiveEarliest<Reveal>();
            c.SendAsync(new Choice(hchoice));
            switch (c.ReceiveEarliest<IResponse>()) {
                case Won x: WriteLine("Even won! :)"); break;
                case Lost x: WriteLine("Even lost :("); break;
                default: Debug.Assert(false); break;
            }
        }

        static void ClientOdd(ServerLink server) {
            bool choice = true;
            var hchoice = new Hiding<bool>(choice, salt: 0x78543564);
            var c = server.Connection<O, HChoice>(new HChoice(hchoice.Hidden(server.address)));
            c.ReceiveEarliest<Reveal>();
            c.SendAsync(new Choice(hchoice));
            switch (c.ReceiveEarliest<IResponse>()) {
                case Won x: WriteLine("Odd won! :)"); break;
                case Lost x: WriteLine("Odd lost :("); break;
                default: Debug.Assert(false); break;
            }
        }

        internal static Session Players = new Session(Server, ClientOdd, ClientEven);
    }
    struct O : Client { }
    struct E : Client { }

    sealed class HChoice : Args<int>, Dir<O, S>, Dir<E, S> { internal HChoice(int _1) { _ = _1; } }
    sealed class Reveal : Dir<S, E>, Dir<S, O> { }
    sealed class Choice : Args<Hiding<bool>>, Dir<O, S>, Dir<E, S> { internal Choice(Hiding<bool> _1) { _ = _1; } }

    interface IResponse : Dir<S, O>, Dir<S, E> { }
    sealed class Won : IResponse { }
    sealed class Lost : IResponse { }
}