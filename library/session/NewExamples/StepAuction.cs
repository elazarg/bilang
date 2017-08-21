using System.Diagnostics;
using System.Threading.Tasks;
using static System.Console;

static class StepAuction {
    
    private interface B : Client { }
    private interface H : Client { }

    private sealed class StartAuction: Args<uint>, Dir<H, S> { internal StartAuction(uint _1) { _ = _1; } }
    private sealed class Offer : Args<uint>, Dir<S, Client>, Dir<B, S> { internal Offer(uint _1) { _ = _1; } }

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

    static async Task ClientHost(UpLink<H> server) {
        WriteLine($"Host connecting");
        server.Send(new StartAuction(50));
        while (true) {
            WriteLine($"Host Receiving");
            uint currentPrice = await server.ReceiveEarliest<Offer>(@public: true);
            WriteLine($"Host Received {currentPrice}");
            if (currentPrice > 80) {
                server.Send(new Stop());
            } else {
                server.Send(new Continue());
            }
        }
    }
    
    static async Task ClientBidder(UpLink<B> server) {
        uint mylast = 0;
        while (true) {
            WriteLine($"Client receiving");
            uint currentOffer = await server.ReceiveEarliest<Offer>(@public: true);
            WriteLine($"Bid {currentOffer}");
            if (currentOffer < 90 && currentOffer != mylast) {
                mylast = currentOffer + 5;
                WriteLine($"Bidding {mylast}");
                await server.SendAsync(new Offer(mylast));
                WriteLine($"Done");
            }
            switch (await server.ReceiveEarliest<Result>()) {
                case Accepted x: goto exit;
                case AnotherRound x: break;
                default: Debug.Assert(false); break;
            }
        } 
        exit:
        WriteLine($"Finish at {mylast}");
    }

    internal static Task[] Players(BC bc) => new Task[] {
        Server(new PublicLink(bc, 0)),
        ClientHost(new UpLink<H>(bc, 1, 0)),
        ClientBidder(new UpLink<B>(bc, 2, 0)),
        ClientBidder(new UpLink<B>(bc, 3, 0))
    };

}
