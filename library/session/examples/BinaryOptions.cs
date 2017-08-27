using System.Diagnostics;
using static System.Console;
using static Combinators;
using System;

static class BinaryOptions {

    private struct Oracle : Client { }
    private struct L : Client { }
    private struct M : Client { }

    private sealed class StockPrice : Args<uint>, Dir<Oracle, S>, Dir<S, Client>, Dir<S, L>, Dir<S, M> { internal StockPrice(uint _1) { _ = _1; } }
    private sealed class Ready : Dir<S, Oracle> { }

    private interface Response : Dir<S, M>, Dir<S, L> { }
    private sealed class Won : Response { }
    private sealed class Lost : Response { }


    static void Server(PublicLink @public) {
        (var oracle, uint firstStockPrice) = @public.Connection<StockPrice, Oracle>().Accept();
        @public.Publish(new StockPrice(firstStockPrice));
        var ((more, _), (less, _)) = Parallel(@public.Connection<M>(), @public.Connection<L>());
        oracle.Send(new Ready());
        uint secondStockPrice = oracle.Receive<StockPrice>().Accept();
        if (secondStockPrice > firstStockPrice) {
            more.Send(new Won());
            less.Send(new Lost());
        } else {
            more.Send(new Lost());
            less.Send(new Won());
        }
    }

    static void ClientOracle(ServerLink server) {
        var c = server.Connection<Oracle, StockPrice>(new StockPrice(16));
        c.ReceiveEarliest<Ready>();
        c.SendAsync(new StockPrice(18));
    }

    static void ClientMore(ServerLink server) {
        uint price = server.ReceiveLatestPublic<StockPrice>();
        var c = server.Connection<M>();
        switch (c.ReceiveEarliest<Response>()) {
            case Won x: WriteLine("More won! :)"); break;
            case Lost x: WriteLine("More lost :("); break;
            default: Debug.Assert(false); break;
        }
    }

    // Exact copy of Client more up to s/M/L/
    static void ClientLess(ServerLink server) {
        uint price = server.ReceiveLatestPublic<StockPrice>();
        var c = server.Connection<L>();
        switch (c.ReceiveEarliest<Response>()) {
            case Won x: WriteLine("Less won! :)"); break;
            case Lost x: WriteLine("Less lost :("); break;
            default: Debug.Assert(false); break;
        }
    }

    internal static Action[] Players(BC bc) => new Action[] {
        () => Server(new PublicLink(bc, 0)),
        () => ClientOracle(new ServerLink(bc, 1)),
        () => ClientMore(new ServerLink(bc, 2)),
        () => ClientLess(new ServerLink(bc, 3))
    };

}
