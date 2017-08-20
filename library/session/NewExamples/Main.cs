using System;
using System.Threading.Tasks.Schedulers;


class MainTest {
    public static void Main() {
        BC bc = new BC();
        //OrderedTaskScheduler.Start(PuzzleNew.Players(bc));
        //OrderedTaskScheduler.Start(MontyHallNew.Players(bc));
        //OrderedTaskScheduler.Start(BinaryOptionsNew.Players(bc));
        bc.Start(SimultaneousNew.Players(bc));
        Console.ReadKey();
    }
}
