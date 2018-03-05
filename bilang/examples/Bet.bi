var Race : role = 0x225325;
join Gambler;
yield Gambler(b: int);
yield Race(winner: int);
if (winner == undefined || winner == b) {
    transfer Race.value from Race to Gambler;
} else {
    transfer Gambler.value from Gambler to Race;
}
