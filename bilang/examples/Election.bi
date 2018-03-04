join many Voters;
var total: int = 0;
for yield Voter(vote: int) from Voters where vote == -1 || vote == 1 {
    total := total + vote;
}
var Result : bool = total > 0;
