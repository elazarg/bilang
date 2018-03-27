join Owner(minimal: int);
var maxValue: int = minimal;
var Winner: role = Owner;
var secondMaxValue: int = 0;
join many Bidders;
for yield Bidder(offer: int) from Bidders {
    // to make this commutative we'll need >= and collect the set of offers,
    // then select at random
    if (offer > maxValue) {
        secondMaxValue := maxValue;
        maxValue := offer;
        Winner := Bidder;
    } else if (offer > secondMaxValue) {
        secondMaxValue := offer;
    }
}
transfer secondMaxValue from Winner to Owner;
