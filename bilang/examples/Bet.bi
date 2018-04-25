type options = {1, 2, 3}

join Race() $ 100 where Race == 0x225325;
join Gambler(bet: options) $ 100;
yield Race(winner: options);
withdraw (Race.winner == null || Race.winner == Gambler.bet)
    ? { Race -> 0; Gambler -> 100 }
    : { Race -> 100; Gambler -> 0 }
