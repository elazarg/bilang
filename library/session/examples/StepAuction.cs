using System.Diagnostics;
using System.Threading.Tasks;
using static System.Console;

static class StepAuction {
    
    private struct B : Client { }
    private struct H : Client { }

    private sealed class StartAuction: Args<uint>, Dir<H, S> { internal StartAuction(uint _1) { _ = _1; } }
    private sealed class Offer : Args<uint>, Dir<S, B>, Dir<S, H>, Dir<S, Client>, Dir<B, S> { internal Offer(uint _1) { _ = _1; } }

    private interface Response : Dir<H, S> { }
    private sealed class Stop : Response { }
    private sealed class Continue : Response { }

    private interface Result : Dir<S, B> { }
    private sealed class Accepted : Result { }
    private sealed class AnotherRound : Result { }


    static async Task Server(PublicLink @public) {
        WriteLine($"Server awaiting Connection");
        (var host, uint minimal) = await @public.Connection<StartAuction, H>();
        uint currentOffer = minimal;
        WriteLine($"Server publishing");
        @public.Publish(new Offer(currentOffer));
        DownLink<B> bidder = null;
        while (true) {
            WriteLine($"Server awaiting offer");
            (var newBidder, uint newOffer) = await @public.Connection<Offer, B>();
            WriteLine($"Server received offer {newOffer} from {newBidder.address}. Publishing");
            @public.Publish(new Offer(currentOffer));
            if (newOffer > currentOffer) {
                currentOffer = newOffer;
                bidder = newBidder;
                switch (await host.Receive<Response>()) {
                    case Stop x:
                        bidder.Send(new Accepted());
                        goto exit;
                    case Continue x:
                        bidder.Send(new AnotherRound());
                        break;
                    default: Debug.Assert(false); break;
                }
            }
        }
        exit:;
    }

    static async Task ClientHost(ServerLink server) {
        WriteLine($"Host connecting");
        var c = await server.Connection<H, StartAuction>(new StartAuction(50));
        while (true) {
            WriteLine($"Host Receiving");
            uint currentPrice = await server.ReceiveLatestPublic<Offer>();
            WriteLine($"Host Received {currentPrice}");
            if (currentPrice > 80) {
                c.Send(new Stop());
            } else {
                c.Send(new Continue());
            }
        }
    }
    
    static async Task ClientBidder(ServerLink server) {
        uint mylast = 0;
        while (true) {
            WriteLine($"Client receiving");
            uint currentOffer = await server.ReceiveLatestPublic<Offer>();
            WriteLine($"Bid {currentOffer}");
            if (currentOffer < 90 && currentOffer != mylast) {
                mylast = currentOffer + 5;
                var c = await server.Connection<B, Offer>(new Offer(mylast));
                switch (await c.ReceiveEarliest<Result>()) {
                    case Accepted x: goto exit;
                    case AnotherRound x: break;
                    default: Debug.Assert(false); break;
                }
            }
        } 
        exit:
        WriteLine($"Finish at {mylast}");
    }

    internal static Task[] Players(BC bc) => new Task[] {
        Server(new PublicLink(bc, 0)),
        ClientHost(new ServerLink(bc, 1)),
        ClientBidder(new ServerLink(bc, 2)),
        ClientBidder(new ServerLink(bc, 3))
    };

}
