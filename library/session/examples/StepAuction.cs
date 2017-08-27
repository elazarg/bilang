using System;
using System.Diagnostics;
using static System.Console;

static class StepAuction {
    
    private struct B : Client { }
    private struct H : Client { }

    private sealed class StartAuction: Args<uint>, Dir<H, S> { internal StartAuction(uint _1) { _ = _1; } }
    private sealed class Offer : Args<uint>, Dir<S, B>, Dir<S, H>, Dir<S, Client>, Dir<B, S> { internal Offer(uint _1) { _ = _1; } }

    private interface IResponse : Dir<H, S> { }
    private sealed class Stop : IResponse { }
    private sealed class Continue : IResponse { }

    private interface IResult : Dir<S, B> { }
    private sealed class Accepted : IResult { }
    private sealed class AnotherRound : IResult { }


    static void Server(PublicLink @public) {
        (var host, uint minimal) = @public.Connection<StartAuction, H>().Accept();
        uint currentOffer = minimal;
        @public.Publish(new Offer(currentOffer));
        DownLink<B> bidder = null;
        while (true) {
            (var newBidder, uint newOffer) = @public.Connection<Offer, B>().Accept();
            @public.Publish(new Offer(currentOffer));
            if (newOffer > currentOffer) {
                currentOffer = newOffer;
                bidder = newBidder;
                switch (host.Receive<IResponse>().Accept()) {
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

    static void ClientHost(ServerLink server) {
        var c = server.Connection<H, StartAuction>(new StartAuction(50));
        while (true) {
            uint currentPrice = server.ReceiveLatestPublic<Offer>();
            if (currentPrice > 80) {
                c.Send(new Stop());
            } else {
                c.Send(new Continue());
            }
        }
    }
    
    static void ClientBidder(ServerLink server) {
        uint mylast = 0;
        while (true) {
            uint currentOffer = server.ReceiveLatestPublic<Offer>();
            if (currentOffer < 90 && currentOffer != mylast) {
                mylast = currentOffer + 5;
                var c = server.Connection<B, Offer>(new Offer(mylast));
                switch (c.ReceiveEarliest<IResult>()) {
                    case Accepted x: goto exit;
                    case AnotherRound x: break;
                    default: Debug.Assert(false); break;
                }
            }
        } 
        exit:
        WriteLine($"Finish at {mylast}");
    }

    internal static Session Players = new Session(Server, ClientHost, ClientBidder, ClientBidder);
}
