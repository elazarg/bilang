using System.Diagnostics;
using System.Threading.Tasks;
using static System.Console;
using static Combinators;


static class BinaryOptions {

    private struct Oracle : Client { }
    private struct L : Client { }
    private struct M : Client { }

    private sealed class StockPrice : Args<uint>, Dir<Oracle, S>, Dir<S, Client>, Dir<S, L>, Dir<S, M> { internal StockPrice(uint _1) { _ = _1; } }
    private sealed class Ready : Dir<S, Oracle> { }

    private interface Response : Dir<S, M>, Dir<S, L> { }
    private sealed class Won : Response { }
    private sealed class Lost : Response { }


    static async Task Server(PublicLink @public) {
        (var oracle, uint firstStockPrice) = await @public.Connection<StockPrice, Oracle>();
        @public.Publish(new StockPrice(firstStockPrice));
        var ((more, _), (less, _)) = await Parallel(@public.Connection<M>(), @public.Connection<L>());
        oracle.Send(new Ready());
        uint secondStockPrice = await oracle.Receive<StockPrice>();
        if (secondStockPrice > firstStockPrice) {
            more.Send(new Won());
            less.Send(new Lost());
        } else {
            more.Send(new Lost());
            less.Send(new Won());
        }
    }

    static async Task ClientOracle(UpLink<Oracle> server) {
        server.Send(new StockPrice(16));
        await server.ReceiveEarliest<Ready>();
        await server.SendAsync(new StockPrice(18));
    }

    static async Task ClientMore(ServerLink server) {
        uint price = await server.ReceiveLatestPublic<StockPrice>();
        var c = await server.Connection<M>();
        switch (await c.ReceiveEarliest<Response>()) {
            case Won x: WriteLine("More won! :)"); break;
            case Lost x: WriteLine("More lost :("); break;
            default: Debug.Assert(false); break;
        }
    }

    // Exact copy of Client more up to s/M/L/
    static async Task ClientLess(ServerLink server) {
        uint price = await server.ReceiveLatestPublic<StockPrice>();
        var c = await server.Connection<L>();
        switch (await c.ReceiveEarliest<Response>()) {
            case Won x: WriteLine("Less won! :)"); break;
            case Lost x: WriteLine("Less lost :("); break;
            default: Debug.Assert(false); break;
        }
    }

    internal static Task[] Players(BC bc) => new Task[] {
        Server(new PublicLink(bc, 0)),
        ClientOracle(new UpLink<Oracle>(bc, 1, 0)),
        ClientMore(new ServerLink(bc, 2)),
        ClientLess(new ServerLink(bc, 3))
    };

}
