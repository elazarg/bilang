using System;
using System.Diagnostics;
using System.Threading.Tasks;
using System.Threading.Tasks.Schedulers;
using static System.Console;


static class PuzzleNew {

    interface Q : All { }
    interface A : All { }
    interface S : All { }

    private sealed class Question : Args<int>, Dir<Q, S>, Dir<S, All> { internal Question(int _1) { _ = _1; } }
    private sealed class Answer : Args<(int, int)>, Dir<A, S>, Dir<S, Q> { internal Answer(int _1, int _2) { _ = (_1, _2); } }

    private interface Response : Dir<S, A> { }
    private sealed class Accepted : Response { }
    private sealed class Rejected : Response { }


    static async Task Server(PublicLink<S> pub) {
        WriteLine($"Server is waiting for connection");
        (var asker, int riddle) = await pub.Connection<Question, Q>(); WriteLine($"Server received {riddle} from {asker}");
        // publishing without waiting does not work with single point for pending/delivered
        // it should be extracted out to the clients, or as a public state
        pub.Publish(new Question(riddle)); WriteLine("Server receives...");
        while (true) {
            var (solver, (m, n)) = await pub.Connection<Answer, A>(); WriteLine($"Server received {m} {n} from {solver}");
            if (m * n == riddle) {
                solver.Send(new Accepted());
                asker.Send(new Answer(3, 5)); WriteLine("Server done");
                break;
            } else {
                solver.Send(new Rejected());
            }
        }
    }


    static async Task ClientQuestion(DirLink<Q, S> link) {
        WriteLine($"Client Q sends question");
        await link.SendAsync(new Question(15));
        var (m, n) = await link.Receive<Answer>(); WriteLine($"Client Q received solution ({m}, {n})");
        WriteLine($"Client Q done");
    }

    static async Task ClientAnswer(DirLink<A, S> link) {
        WriteLine($"Client A fetches question");
        int riddle = await link.Receive<Question>(); WriteLine($"Client A sends solution {(3, 5)}");
        // pretend we are solving the problem
        await link.SendAsync(new Answer(3, 5)); WriteLine($"Client A sent solution");
        switch (await link.Receive<Response>()) {
            case Accepted x: WriteLine("Good answer"); break;
            case Rejected x: WriteLine("Bad answer"); break;
            default: Debug.Assert(false); break;
        }
        WriteLine($"Client A done");
    }

    public static void Main() {
        BC bc = new BC();
        OrderedTaskScheduler.Start(
            Server(new PublicLink<S>(bc, 0)),
            ClientQuestion(new DirLink<Q, S>(bc, 1, 0)),
            ClientAnswer(new DirLink<A, S>(bc, 2, 0))
        );

        Console.ReadKey();
    }
}
