using System;
using System.Diagnostics;
using static System.Console;

static class StepAuction {
    internal static Session Players = new Session(Server,
        s => ClientHost(s, initial: 50, stopping: 65),
        s => ClientBidder(s, max: 66),
        s => ClientBidder(s, max: 108)
    );

    static void Server(PublicLink @public) {
        (var host, uint minimal) = @public.Connection<StartAuction, H>().Accept();
        @public.Publish(new NewBid((host.address, minimal)));
        uint currentOffer = minimal;
        DownLink<B> bidder = null;
        long time = @public.Now();
        do {
            (var newBidder, uint newOffer) = @public.Connection<Offer, B>().Accept();
            if (newOffer <= currentOffer) {
                continue;
            }
            @public.Publish(new NewBid((newBidder.target, newOffer)));
            currentOffer = newOffer;
            bidder = newBidder;
        } while (@public.Now() < time + 2050000);
        @public.Publish(new AuctionOver((bidder.target, currentOffer)));
    }

    static void ClientHost(ServerLink server, uint initial, uint stopping) {
        var c = server.Connection<H, StartAuction>(new StartAuction(initial));
        (uint winner, uint offer) = server.ReceiveLatestPublic<AuctionOver>();
        WriteLine($"Will get {offer} from {winner}");
    }
    
    static void ClientBidder(ServerLink server, uint max) {
        uint myOffer = 0;
        // not really a connection at all
        while (true) {
            switch (server.ReceiveLatestPublic<IStateChange>()) {
                case NewBid a:
                    (uint bidder, uint offer) = a;
                    if (bidder != server.address) {
                        if (offer > max) {
                            WriteLine("I give up");
                            return;
                        } else {
                            myOffer = Math.Min(max, offer + 5);
                            WriteLine("Trying again");
                            server.Send<B, Offer>(new Offer(myOffer));
                        }
                    }
                    continue;
                case AuctionOver a:
                    (uint winner, uint Lastoffer) = a;
                    if (winner == server.address)
                        WriteLine("I won");
                    else
                        WriteLine("I lost");
                    return;
                default: Debug.Assert(false); break;
            }
            return;
        }
    }

    

    private struct B : Client { }
    private struct H : Client { }
    
    private sealed class StartAuction : Args<uint>, Dir<H, S> { internal StartAuction(uint _1) { _ = _1; } }
    private sealed class Offer : Args<uint>, Dir<B, S> { internal Offer(uint _1) { _ = _1; } }

    private interface IResponse : Dir<H, S> { }
    private sealed class Stop : IResponse { }
    private sealed class Continue : IResponse { }

    private interface IStateChange : Dir<S, B> { }
    private sealed class NewBid : Args<(uint, uint)>, IStateChange, Dir<S, H>, Dir<S, Client> { internal NewBid((uint, uint) _1) { _ = _1; } }
    private sealed class AuctionOver : Args<(uint, uint)>, IStateChange, Dir<S, H>, Dir<S, B>, Dir<S, Client> { internal AuctionOver((uint, uint) _1) { _ = _1; } }

}
