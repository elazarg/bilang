using static SessionLib;
using static CoreLib;
using static ClientSessionLib;

class STPG {
    static async void Server() {
        var ((even, even_payment), (odd, odd_payment)) = await Parallel(Connect<Money>("E"), Connect<Money>("O"));
        using (even) {
            using (odd) {
                var (even_choice, odd_choice) = await Independent<bool, bool>(even, odd);
                if (odd_choice == null && even_choice == null) {
                    //repeat????
                    return;
                }
                if (odd_choice == null || even_choice == odd_choice) {
                    Pay(even, even_payment, odd_payment);
                } else {
                    Pay(odd, even_payment, odd_payment);
                }
            }
        }
    }

    static Contract s;

    static async void ClientPlayer(string tag, bool choice) {
        UpwardConnection c = await s.Connect(tag, new Money());
        await c.Hide(choice, until: "Open");
        // TODO: add finishing message to show the user
    }
}
