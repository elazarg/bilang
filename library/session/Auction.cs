using static SessionLib;
using static CoreLib;
using static ClientSessionLib;
using System;

static class ParallelBlindAuction {
    private static Connection FindWinner(Connection host, Connection[] bidders, int?[] bids) {
        int max = 0;
        Connection winner = host;
        for (int i = 0; i < bids.Length; i++) {
            int b = bids[i] ?? 0;
            if (b > max) {
                max = b;
                winner = bidders[i];
            }
        }
        return winner;
    }

    static async void Server() {
        var (host, last_bid) = await Connect<int>("Host");
        using (host) {
            var bidders = await ConnectMany("Offer",
                until: host.Receive<bool>("Continue"));
            Notify("Place bids", bidders);
            var bids = await Independent<int>(bidders);
            var winner = FindWinner(host, bidders, bids);
            Declare($"{winner} is the winner");
            foreach (var bidder in bidders) {
                string msg;
                if (bidder.address == winner.address) {
                    msg = "You won!";
                } else {
                    msg = "Bidding over, you've lost";
                }
                bidder.Notify(msg);
                bidder.Dispose();
            }
        }
    }

    static Contract s;

    static async void ClientHost() {
        var c = await s.Connect("Host", 50);
        await System.Threading.Tasks.Task.Delay(2000);
        await c.SendAsync("Continue");
        
    }

    static async void ClientOffer(int amount) {
        var c = await s.Connect("Offer");
        await c.ReceiveNotification("Place bids");
        await c.Hide(amount, until: "Reveal");
        Console.WriteLine(await c.ReceiveNotification());
    }
}


static class EitherAuction {
    
    static async void Server() {
        (Connection host, Money last_bid) = await Connect<Money>("Host");
        Connection winner = host;
         while (true) {
            // Idea: have a `Global` struct for visible state
            // FIX: This only works accidentally since null can only result from host
            switch (await FirstOf(Connect<Money>("Bid"), host.Receive("Stop"))) {
                case ValueTuple<Connection, Money> bv:
                    (Connection bidder, Money bid) = bv;
                    Require(bid.amount > last_bid.amount);
                    Pay(winner, last_bid);
                    winner = bidder;
                    last_bid = bid;
                    break;
                default: // STOP
                    Declare($"{winner} won!");
                    Pay(host, last_bid);
                    break;
            }
        }
    }

    static Contract s;

    static async void ClientOffer(int max) {
        /* s.ReadPublic<int>("Last bid");
        var c = await s.Connect("Offer", new Money());
        await c.ReceiveNotification("Place bids");
        await c.Hide(amount, until: "Reveal");

        string result = await c.ReceiveNotification();

        System.Console.WriteLine(result);
        */
    }
}
