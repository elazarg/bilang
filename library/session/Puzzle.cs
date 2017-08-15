using static SessionLib;
using static CoreLib;
using static ClientSessionLib;


class Puzzle {
    static async void Server() {
        (var a, (int q, Money prize)) = await Connect<(int, Money)>("Pose riddle",
            require: qp => qp.Item2.amount == 80);
        using (a) {
            Publish("Question", q);
            (var solver, (int m, int n)) = await Connect<(int, int)>("Factor", require: mn => {
                (var m1, var n1) = mn;
                return m1 != 1 && n1 != 1 && m1 * n1 == q;
            });
            using (solver) {
                a.Notify($"Answer", (m, n));
                Pay(solver, prize);
            }
        }
    }

    static Contract s;

    static async void ClientA() {
        var c = await s.Connect("Pose riddle", (15, new Money(80)));
        (var m, var n) = await c.ReceiveNotification<(int, int)>();
        System.Console.WriteLine($"The solution is {m} * {n}");
    }

    static async void ClientSolver() {
        int value = s.Read<int>("Question");
        (int, int)? nfs = Solve(value);
        if (nfs is null)
            return;
        var c = await s.Connect("Factor", ((int, int))nfs);
        string result = await c.ReceiveNotification();
    }

    private static (int, int)? Solve(int value) {
        (int, int)? fs = null;
        for (int i = 2; i < value; i++)
            if (i * (value / i) == value)
                fs = (i, value / i);
        return fs;
    }
}


class PuzzleSpecific {
    static async void Server() {
        (var a, Money prize) = await Connect<Money>("Q");
        var solver = await Connect("A");
        using (a) {
            using (solver) {
                a.Notify("Solver connected");
                int q = await a.Receive<int>();
                solver.Notify("Riddle", q);
                (int m, int n) = await solver.Receive<(int, int)>(require: mn => {
                    (var m1, var n1) = mn;
                    return m1 != 1 && n1 != 1 && m1 * n1 == q;
                });
                a.Notify($"Answer", (m, n));
                Pay(solver, prize);
            }
        }
    }

    static Contract s;

    static async void ClientA() {
        var c = await s.Connect("Pose riddle", new Money(80));
        await c.ReceiveNotification("Solver connected");
        await c.SendAsync(15);
        (var m, var n) = await c.ReceiveNotification<(int, int)>();
        System.Console.WriteLine($"The solution is {m} * {n}");
    }

    static async void ClientSolver() {
        int value = s.Read<int>("Question");
        (int, int)? nfs = Solve(value);
        if (nfs is null)
            return;
        var c = await s.Connect("Factor", ((int, int))nfs);
        string result = await c.ReceiveNotification();
    }

    private static (int, int)? Solve(int value) {
        (int, int)? fs = null;
        for (int i = 2; i < value; i++)
            if (i * (value / i) == value)
                fs = (i, value / i);
        return fs;
    }
}
