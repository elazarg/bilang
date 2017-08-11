using static SessionLib;
using static CoreLib;

class BinaryOptions {
    static async void Run() {
        using (var oracle = await Connect(id: 0x2357465)) {
            ((var more, var more_bet), (var less, var less_bet)) = await Parallel(Connect<Money>(tag: ">"), Connect<Money>(tag: "<"));
            {
                if (await oracle.Receive<bool>("Has stock price went up?"))
                    Pay(more, less_bet, more_bet);
                else
                    Pay(less, less_bet, more_bet);
            }
        }
    }
}
