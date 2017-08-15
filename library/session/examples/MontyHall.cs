using static SessionLib;
using static CoreLib;
using static ClientSessionLib;
using System.Threading.Tasks;

static class MontyHall {
    public enum Door { a, b, c }

    public static async void Server() {
        var (host, host_money) = await Connect<Money>("Host");
        using (host) {
            var hiddenCar = await host.Hide<Door>();
            var (guest, guest_money) = await Connect<Money>("Guest");
            using (guest) {
                var door1 = await guest.Receive<Door>();
                host.Notify("Guest chose", door1);
                var goat = await host.Receive<Door>(require: g => g != door1);
                guest.Notify("Goat behind door", goat);
                var door2 = await guest.Receive<Door>(require: d => d != goat);

                Door car = await host.Open(hiddenCar) ?? door2;
                if (car == goat || car == door2) {
                    Pay(guest, host_money, guest_money);
                    guest.Notify("You won!");
                    host.Notify("You lost!");
                } else {
                    Pay(host, host_money, guest_money);
                    host.Notify("You won!");
                    guest.Notify("You lost!");
                }
            }
        }
    }

    public static Contract s;

    public static async void ClientHost(Door car) {
        UpwardConnection c = await s.Connect("Host", new Money());
        var hiddenCar = await c.Hide(car);
        Door door1 = await c.ReceiveNotification<Door>("Guest chose");
        Door goat = door1 == car ? Door.c : Door.b;
        await c.SendAsync(goat);
        await c.ReceiveNotification("Reveal");
        await c.OpenAsync(hiddenCar);
        string result = await c.ReceiveNotification<string>();
        System.Console.WriteLine(result);
    }

    public static async void ClientGuest() {
        UpwardConnection c = await s.Connect("Guest", new Money());
        await c.SendAsync(Door.a);
        Door goat = await c.ReceiveNotification<Door>("Goat behind door");
        Door door2 = goat == Door.c ? Door.b : Door.c;
        await c.SendAsync(door2);
        string result = await c.ReceiveNotification<string>();
        System.Console.WriteLine(result);
    }
}
