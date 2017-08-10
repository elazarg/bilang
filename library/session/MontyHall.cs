using static SessionLib;
using static CoreLib;
using static Utils;

class MontyHall {
    enum Door { a, b, c }
    static async void Run() {
        (var host, Money host_money) = await Connect<Money>("Host");
        using (host) {
            var hiddenCar = await host.Hide<Door>();
            (var guest, Money guest_money) = await Connect<Money>("Guest");
            using (guest) {
                var door1 = await guest.Receive<Door>("Choose first door");
                var goat = await host.Receive<Door>("Reveal goat",
                    require: g => g != door1);
                var door2 = await guest.Receive<Door>("Do you want to switch?",
                    require: d => d != goat);

                Door car = await host.Open(hiddenCar) ?? door2;
                if (car == goat || car == door2)
                    Pay(guest, host_money, guest_money);
                else
                    Pay(host, host_money, guest_money);
            }
        }
    }
}
