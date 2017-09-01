using System;

class MainTest {
    public static void Main() {
        var c = new Controller();
        //c.Start(Puzzle.Players);
        //c.Start(MontyHall.MontyHall.Players);
        //c.Start(BinaryOptions.Players);
        c.Start(Simultaneous.Simultaneous.Players);
        //c.Start(StepAuction.Players);
    }
}
