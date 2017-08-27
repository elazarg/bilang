using System;

class MainTest {
    public static void Main() {
        var c = new Controller();
        BC bc = new BC(c);
        //c.Start(bc, Puzzle.Players(bc));
        //c.Start(bc, MontyHall.MontyHall.Players(bc));
        c.Start(BinaryOptions.Players);
        //c.Start(bc, Simultaneous.Simultaneous.Players(bc));
        //c.Start(bc, StepAuction.Players(bc));
    }
}
