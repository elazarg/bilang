using static SessionLib;
using static CoreLib;

class STPG {
    static async void Play() {
        ((var even, var even_payment), (var odd, var odd_payment)) = await Parallel(Connect<Money>("E"), Connect<Money>("O"));
        using (even) {
            using (odd) {
                var choices = await Independent<bool, bool>(even, odd);
                var even_choice = choices.Item1;
                var odd_choice = choices.Item2;
                if (odd_choice == null && even_choice == null) {
                    //repeat????
                    return;
                }
                if (odd_choice == null || even_choice == odd_choice)
                    Pay(even, even_payment, odd_payment);
                else
                    Pay(odd, even_payment, odd_payment);
            }
        }
    }
}
