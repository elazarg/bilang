using System;
using System.Threading.Tasks.Schedulers;


class MainTest {
    public static void Main() {
        BC bc = new BC();
        //OrderedTaskScheduler.Start(PuzzleNew.Players(new BC()));
        //OrderedTaskScheduler.Start(MontyHallNew.Players(new BC()));
        OrderedTaskScheduler.Start(BinaryOptionsNew.Players(new BC()));
        Console.ReadKey();
    }
}
