using static SessionLib;
using static CoreLib;
using static ClientSessionLib;

class BinaryOptions {
    static async void Run() {
        using (var oracle = await Connect("Oracle", id: 0x2357465)) {
            ((var more, var more_bet), (var less, var less_bet)) = await Parallel(Connect<Money>(tag: ">"), Connect<Money>(tag: "<"));
            {
                if (await oracle.Receive<bool>("Has stock price went up?"))
                    Pay(more, less_bet, more_bet);
                else
                    Pay(less, less_bet, more_bet);
            }
        }
    }

    static Contract s;
    
    static async void More() {
        var c = await s.Connect(">", new Money());
    }

    static async void Less() {
        var c = await s.Connect("<", new Money());
    }

    static async void Oracle() {
        var c = await s.Connect("Oracle");
        await c.ReceiveNotification("Has stock price went up?");
        await c.SendAsync(true);
    }
}
