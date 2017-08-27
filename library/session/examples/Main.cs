using System;

class MainTest {
    public static void Main() {
        BC bc = new BC();
        //bc.Start(Puzzle.Players(bc));
        //bc.Start(MontyHall.MontyHall.Players(bc));
        bc.Start(BinaryOptions.Players(bc));
        //bc.Start(Simultaneous.Simultaneous.Players(bc));
        //bc.Start(StepAuction.Players(bc));
    }
}
