using static SessionLib;
using static CoreLib;
using static Utils;

static class Auction {
    static async void NaiveAuction() {
        var (host, last_bid) = await Connect<int>("Host");
        using (host) {
            while (true) {
                (var bidder, var amount) = await Connect<Money>("Offer", require: m => m.amount > last_bid);
                using (bidder) {
                    if (!await host.Receive<bool>("Continue")) {
                        Declare($"{bidder} won!");
                        Pay(host, amount);
                        break;
                    }
                    Pay(bidder, amount);
                    last_bid = amount.amount;
                }
            }
        }
    }

    static async void ParallelBlindAuction() {
        var (host, last_bid) = await Connect<int>("Host");
        using (host) {
            var bidders = await ConnectMany("Offer",
                until: host.Receive<bool>("Continue"));
            var bids = await Independent<int>(bidders);
            var winner = FindWinner(host, bidders, bids);
            Declare($"{winner} is the winner");
        }
    }

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
    static async void UnionAuction() {
        var (host, money) = await Connect<Money>("Host");
        using (host) {
            var last_bid = money;
            var last_bidder = host;
            while (true) {
                // No union types
                dynamic bidder_or_nothing = await FirstOf(
                    host.Receive<Nothing>("Continue"),
                    Connect<Money>("Offer", require: m => m.amount > last_bid.amount));
                if (bidder_or_nothing is Nothing) {
                    Declare($"{last_bidder} won!");
                    Pay(host, last_bid);
                    break;
                }
                var bidder = bidder_or_nothing;
                Pay(last_bidder, last_bid);
                last_bidder.Dispose();
                last_bid = bidder.Initial.amount;
                last_bidder = bidder;
            }
        }
    }

}
