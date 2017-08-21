using System;
using System.Diagnostics;
using System.Threading.Tasks;
using static System.Console;
using static Combinators;
using static Utils;


static class SimultaneousNew {
    
    private interface O : Client { }
    private interface E : Client { }

    private sealed class HChoice : Args<int>, Dir<O, S>, Dir<E, S> { internal HChoice(int _1) { _ = _1; } }
    private sealed class Reveal : Dir<S, Client> { }
    private sealed class Choice : Args<Hiding<bool>>, Dir<O, S>, Dir<E, S> { internal Choice(Hiding<bool> _1) { _ = _1; } }

    private interface Response : Dir<S, O>, Dir<S, E> { }
    private sealed class Won : Response { }
    private sealed class Lost : Response { }


    static async Task Server(PublicLink @public) {
        var even = await @public.Connection<E>();
        var odd = await @public.Connection<O>();
        (int even_hchoice, int odd_hchoice) = await Parallel(even.Receive<HChoice>(), odd.Receive<HChoice>());
        Console.WriteLine("1");
        even.Send(new Reveal()); odd.Send(new Reveal());
        Console.WriteLine("2");
        (Hiding<bool> even_choice, Hiding<bool> odd_choice) = await Parallel(even.Receive<Choice>(), odd.Receive<Choice>());
        Console.WriteLine("3");
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

    static async Task ClientEven(UpLink<E> server) {
        bool choice = true;
        await server.SendAsync();
        WriteLine("E");
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
        await server.SendAsync();
        WriteLine("O");
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
        ClientEven(new UpLink<E>(bc, 1, 0)),
        ClientOdd(new UpLink<O>(bc, 2, 0))
    };

}
