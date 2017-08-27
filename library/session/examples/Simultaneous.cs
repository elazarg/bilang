using System;
using System.Diagnostics;
using System.Threading.Tasks;
using static System.Console;
using static Combinators;
using static Utils;

struct O : Client { }
struct E : Client { }

sealed class HChoice : Args<int>, Dir<O, S>, Dir<E, S> { internal HChoice(int _1) { _ = _1; } }
sealed class Reveal : Dir<S, E>, Dir<S, O> { }
sealed class Choice : Args<Hiding<bool>>, Dir<O, S>, Dir<E, S> { internal Choice(Hiding<bool> _1) { _ = _1; } }

interface Response : Dir<S, O>, Dir<S, E> { }
sealed class Won : Response { }
sealed class Lost : Response { }

static class Simultaneous {    
    static async Task Server(PublicLink @public) {
        var ((even, even_hchoice), (odd, odd_hchoice)) = await Parallel(
            // FIX: does not seem to test for E/O
            @public.Connection<HChoice, E>(),
            @public.Connection<HChoice, O>()
        );
        even.Send(new Reveal()); odd.Send(new Reveal());
        (Hiding<bool> even_choice, Hiding<bool> odd_choice) = await Parallel(even.Receive<Choice>(), odd.Receive<Choice>());
        bool even_honest = even_choice.Hidden((uint)even.target) == even_hchoice;
        bool odd_honest = odd_choice.Hidden((uint)odd.target) == odd_hchoice;
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

    static async Task ClientEven(UpLink<E> server) {
        bool choice = true;
        var hchoice = new Hiding<bool>(choice, salt: 0x78573264);
        await server.SendAsync(new HChoice(hchoice.Hidden(server.address)));
        await server.ReceiveEarliest<Reveal>();
        await server.SendAsync(new Choice(hchoice));
        switch (await server.ReceiveEarliest<Response>()) {
            case Won x: WriteLine("Even won! :)"); break;
            case Lost x: WriteLine("Even lost :("); break;
            default: Debug.Assert(false); break;
        }
    }

    static async Task ClientOdd(UpLink<O> server) {
        bool choice = true;
        var hchoice = new Hiding<bool>(choice, salt: 0x78573264);
        await server.SendAsync(new HChoice(hchoice.Hidden(server.address)));
        await server.ReceiveEarliest<Reveal>();
        await server.SendAsync(new Choice(hchoice));
        switch (await server.ReceiveEarliest<Response>()) {
            case Won x: WriteLine("Odd won! :)"); break;
            case Lost x: WriteLine("Odd lost :("); break;
            default: Debug.Assert(false); break;
        }
    }

    internal static Task[] Players(BC bc) => new Task[] {
        Server(new PublicLink(bc, 0)),
        ClientOdd(new UpLink<O>(bc, 2, 0)),
        ClientEven(new UpLink<E>(bc, 1, 0))
    };

}
