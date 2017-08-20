using System;
using System.Diagnostics;
using System.Threading.Tasks;
using static System.Console;
using static Combinators;
using static Utils;


static class SimultaneousNew {
    
    private interface O : Client { }
    private interface E : Client { }
    private interface S { }

    private sealed class HChoice : Args<int>, Dir<O, S>, Dir<E, S> { internal HChoice(int _1) { _ = _1; } }
    private sealed class Reveal : Dir<S, Client> { }
    private sealed class Choice : Args<Hiding<bool>>, Dir<O, S>, Dir<E, S> { internal Choice(Hiding<bool> _1) { _ = _1; } }

    private interface Response : Dir<S, O>, Dir<S, E> { }
    private sealed class Won : Response { }
    private sealed class Lost : Response { }


    static async Task Server(PublicLink<S> @public) {
        var even = await @public.Connection<E>();
        var odd = await @public.Connection<O>();
        (int even_hchoice, int odd_hchoice) = await Parallel(even.Receive<HChoice>(), odd.Receive<HChoice>());
        @public.Publish(new Reveal()); @public.Publish(new Reveal());
        (Hiding<bool> even_choice, Hiding<bool> odd_choice) = await Parallel(even.Receive<Choice>(), odd.Receive<Choice>());
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

    static async Task ClientEven(DirLink<E, S> server) {
        bool choice = true;
        await server.SendAsync();
        WriteLine("E");
        var hchoice = new Hiding<bool>(choice, salt: 0x78573264);
        await server.SendAsync(new HChoice(hchoice.Hidden(server.address)));
        await server.Receive<Reveal>();
        await server.SendAsync(new Choice(hchoice));
        switch (await server.Receive<Response>()) {
            case Won x: WriteLine("Even won! :)"); break;
            case Lost x: WriteLine("Even lost :("); break;
            default: Debug.Assert(false); break;
        }
    }

    static async Task ClientOdd(DirLink<O, S> server) {
        bool choice = true;
        await server.SendAsync();
        WriteLine("O");
        var hchoice = new Hiding<bool>(choice, salt: 0x78573264);
        await server.SendAsync(new HChoice(hchoice.Hidden(server.address)));
        await server.Receive<Reveal>();
        await server.SendAsync(new Choice(hchoice));
        switch (await server.Receive<Response>()) {
            case Won x: WriteLine("Odd won! :)"); break;
            case Lost x: WriteLine("Odd lost :("); break;
            default: Debug.Assert(false); break;
        }
    }

    internal static Task[] Players(BC bc) => new Task[] {
        Server(new PublicLink<S>(bc, 0)),
        ClientEven(new DirLink<E, S>(bc, 1, 0)),
        ClientOdd(new DirLink<O, S>(bc, 2, 0))
    };

}
