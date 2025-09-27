join many Voters;
var total: int = 0;
for yield Voter(vote: int) where vote == -1 || vote == 1
    from Voters {
    total := total + vote;
}
var result : bool = total > 0;
