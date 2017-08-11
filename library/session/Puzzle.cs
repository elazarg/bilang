using static SessionLib;
using static CoreLib;
using static Utils;

class Puzzle {
    static async void Run() {
        (var a, (int q, Money prize)) = await Connect<(int, Money)>("Pose riddle",
            require: qp => qp.Item2.amount == 80);
        using (a) {
            (var solver, (int m, int n)) = await Connect<(int, int)>("Factor", require: mn => {
                (var m1, var n1) = mn;
                return m1 != 1 && n1 != 1 && m1 * n1 == q;
            });
            using (solver) {
                Notify($"{m} * {m} == {q}", a);
                Pay(solver, prize);
            }
        }
    }
}
