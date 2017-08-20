using System;
using System.Diagnostics;
using System.Threading.Tasks;
using static System.Console;
using static Combinators;


static class BinaryOptionsNew {

    private interface Oracle : Client { }
    private interface L : Client { }
    private interface M : Client { }
    private interface S { }

    private sealed class StockPrice : Args<uint>, Dir<Oracle, S>, Dir<S, Client> { internal StockPrice(uint _1) { _ = _1; } }
    private sealed class Ready : Dir<S, Oracle> { }

    private interface Response : Dir<S, M>, Dir<S, L> { }
    private sealed class Won : Response { }
    private sealed class Lost : Response { }


    static async Task Server(PublicLink<S> @public) {
        var (oracle, firstStockPrice) = await @public.Connection<StockPrice, Oracle>();
        // the double publish should be resolved by new messaging system
        @public.Publish(new StockPrice(firstStockPrice));
        @public.Publish(new StockPrice(firstStockPrice));
        var (more, less) = await Parallel(@public.Connection<M>(), @public.Connection<L>());
        oracle.Send(new Ready());
        var secondStockPrice = await oracle.Receive<StockPrice>();
        if (secondStockPrice > firstStockPrice) {
            more.Send(new Won());
            less.Send(new Lost());
        } else {
            more.Send(new Lost());
            less.Send(new Won());
        }
    }

    static async Task ClientOracle(DirLink<Oracle, S> server) {
        server.Send(new StockPrice(16));
        await server.Receive<Ready>();
        await server.SendAsync(new StockPrice(5));
    }

    static async Task ClientMore(DirLink<M, S> server) {
        uint price = await server.Receive<StockPrice>();
        await server.SendAsync();
        switch (await server.Receive<Response>()) {
            case Won x: WriteLine("More won! :)"); break;
            case Lost x: WriteLine("More lost :("); break;
            default: Debug.Assert(false); break;
        }
    }

    // Exact copy of Client more up to s/M/L/
    static async Task ClientLess(DirLink<L, S> server) {
        uint price = await server.Receive<StockPrice>();
        await server.SendAsync();
        switch (await server.Receive<Response>()) {
            case Won x: WriteLine("Less won! :)"); break;
            case Lost x: WriteLine("Less lost :("); break;
            default: Debug.Assert(false); break;
        }
    }

    internal static Task[] Players(BC bc) => new Task[] {
        Server(new PublicLink<S>(bc, 0)),
        ClientOracle(new DirLink<Oracle, S>(bc, 1, 0)),
        ClientMore(new DirLink<M, S>(bc, 2, 0)),
        ClientLess(new DirLink<L, S>(bc, 3, 0))
    };

}
