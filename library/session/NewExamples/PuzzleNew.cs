using System;
using System.Diagnostics;
using System.Threading.Tasks;
using static System.Console;


static class PuzzleNew {

    private interface Q : Client { }
    private interface A : Client { }
    private interface S { }

    private sealed class Question : Args<int>, Dir<Q, S>, Dir<S, Client> { internal Question(int _1) { _ = _1; } }
    private sealed class Answer : Args<(int, int)>, Dir<A, S>, Dir<S, Q> { internal Answer(int _1, int _2) { _ = (_1, _2); } }

    private interface Response : Dir<S, A> { }
    private sealed class Accepted : Response { }
    private sealed class Rejected : Response { }


    static async Task Server(PublicLink<S> @public) {
        (var asker, int riddle) = await @public.Connection<Question, Q>();
        @public.Publish(new Question(riddle));
        while (true) {
            var (solver, (m, n)) = await @public.Connection<Answer, A>();
            if (m * n == riddle) {
                solver.Send(new Accepted());
                asker.Send(new Answer(3, 5));
                break;
            } else {
                solver.Send(new Rejected());
            }
        }
    }

    static async Task ClientQuestion(DirLink<Q, S> server) {
        int q = 15;
        await server.SendAsync(new Question(q));
        var (m, n) = await server.Receive<Answer>();
        WriteLine("Client received answer {m} * {n} == {q}");
    }

    static async Task ClientAnswer(DirLink<A, S> server) {
        int riddle = await server.Receive<Question>();
        // pretend we are solving the problem, then...
        await server.SendAsync(new Answer(3, 5));
        switch (await server.Receive<Response>()) {
            case Accepted x: WriteLine("Good answer"); break;
            case Rejected x: WriteLine("Bad answer" ); break;
            default: Debug.Assert(false); break;
        }
    }

    internal static Task[] Players(BC bc) => new Task[] {
        Server(new PublicLink<S>(bc, 0)),
        ClientQuestion(new DirLink<Q, S>(bc, 1, 0)),
        ClientAnswer(new DirLink<A, S>(bc, 2, 0))
    };

}
