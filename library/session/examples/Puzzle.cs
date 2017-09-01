using System;
using System.Diagnostics;
using static System.Console;


static class Puzzle {

    private struct Q : Client { }
    private struct A : Client { }

    private sealed class Question : Args<int>, Dir<Q, S>, Dir<S, Client>, Dir<S, A> { internal Question(int _1) { _ = _1; } }
    private sealed class Answer : Args<(int, int)>, Dir<A, S>, Dir<S, Q> { internal Answer(int _1, int _2) { _ = (_1, _2); } }

    private interface IResponse : Dir<S, A> { }
    private sealed class Accepted : IResponse { }
    private sealed class Rejected : IResponse { }
    /*
explicit global protocol Puzzle(role S, role P, role Q, role A) {
    connect S to P;
    connect P to A;
    
    connect S to Q;
    question(int) from Q to S;
    question(int) from S to P;
    rec loop {
        connect S to A;
        answer(int, int) from A to S;
        choice at S {
            answer(int, int) from S to Q;
            accepted() from S to A;
        } or {
            rejected() from S to A;
            disconnect S and A;
            continue loop;
        }
    }
}
    */
    static void Server(PublicLink @public) {
        (var asker, int riddle) = @public.Connection<Question, Q>().Accept();
        @public.Publish(new Question(riddle));
        while (true) {
            var (solver, (m, n)) = @public.Connection<Answer, A>().Accept();
            if (m * n == riddle) {
                asker.Send(new Answer(3, 5));
                solver.Send(new Accepted());
            } else {
                solver.Send(new Rejected());
                continue;
            }
            break;
        }
    }

    static void ClientQuestion(ServerLink server) {
        int q = 15;
        var c = server.Connection<Q, Question>(new Question(q));
        WriteLine($"Question: factor {q}");
        var (m, n) = c.ReceiveEarliest<Answer>();
        WriteLine($"Answer {m} * {n} == {q}");
    }

    static void ClientAnswer(ServerLink server) {
        int riddle = server.ReceiveLatestPublic<Question>();
        // pretend we are solving the problem, then...
        var c = server.Connection<A, Answer>(new Answer(3, 5));
        switch (c.ReceiveEarliest<IResponse>()) {
            case Accepted x: WriteLine("Good answer"); break;
            case Rejected x: WriteLine("Bad answer" ); break;
            default: Debug.Assert(false); break;
        }
    }

    internal static Session Players = new Session(Server, ClientQuestion, ClientAnswer);
}
