let Race : role = 0x225325;
join Gambler(b: int);
yield Race(winner: int);
return (Race.winner == undefined || Race.winner == b)
    ? { Race -> 0; Gambler -> 100 }
    : { Race -> 100; Gambler -> 0 }
