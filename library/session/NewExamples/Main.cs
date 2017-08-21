using System;
using System.Threading.Tasks.Schedulers;


class MainTest {
    public static void Main() {
        BC bc = new BC();
        //bc.Start(PuzzleNew.Players(bc));
        //bc.Start(MontyHallNew.Players(bc));
        //bc.Start(BinaryOptionsNew.Players(bc));
        bc.Start(SimultaneousNew.Players(bc));
        //bc.Start(StepAuction.Players(bc));
        Console.ReadKey();
    }
}
