using System.Diagnostics;
using System.Threading.Tasks;
using static System.Console;


static class Puzzle {

    private interface Q : Client { }
    private interface A : Client { }

    private sealed class Question : Args<int>, Dir<Q, S>, Dir<S, Client> { internal Question(int _1) { _ = _1; } }
    private sealed class Answer : Args<(int, int)>, Dir<A, S>, Dir<S, Q> { internal Answer(int _1, int _2) { _ = (_1, _2); } }

    private interface Response : Dir<S, A> { }
    private sealed class Accepted : Response { }
    private sealed class Rejected : Response { }


    static async Task Server(PublicLink @public) {
        (var asker, int riddle) = await @public.Connection<Question, Q>();
        @public.Publish(new Question(riddle));
        while (true) {
            var (solver, (m, n)) = await @public.Connection<Answer, A>();
            if (m * n == riddle) {
                asker.Send(new Answer(3, 5));
                solver.Send(new Accepted());
                break;
            } else {
                solver.Send(new Rejected());
            }
        }
    }

    static async Task ClientQuestion(UpLink<Q> server) {
        int q = 15;
        await server.SendAsync(new Question(q));
        WriteLine($"Question: factor {q}");
        var (m, n) = await server.ReceiveEarliest<Answer>();
        WriteLine($"Answer {m} * {n} == {q}");
    }

    static async Task ClientAnswer(UpLink<A> server) {
        int riddle = await server.ReceiveEarliest<Question>(@public: true);
        // pretend we are solving the problem, then...
        await server.SendAsync(new Answer(3, 5));
        switch (await server.ReceiveEarliest<Response>()) {
            case Accepted x: WriteLine("Good answer"); break;
            case Rejected x: WriteLine("Bad answer" ); break;
            default: Debug.Assert(false); break;
        }
    }

    internal static Task[] Players(BC bc) => new Task[] {
        Server(new PublicLink(bc, 0)),
        ClientQuestion(new UpLink<Q>(bc, 1, 0)),
        ClientAnswer(new UpLink<A>(bc, 2, 0))
    };

}
