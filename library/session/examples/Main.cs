using System;
using System.Threading.Tasks.Schedulers;


class MainTest {
    public static void Main() {
        BC bc = new BC();
        bc.Start(Puzzle.Players(bc));
        //bc.Start(MontyHall.Players(bc));
        //bc.Start(BinaryOptions.Players(bc));
        //bc.Start(Simultaneous.Players(bc));
        //bc.Start(StepAuction.Players(bc));
        Console.ReadKey();
    }
}
