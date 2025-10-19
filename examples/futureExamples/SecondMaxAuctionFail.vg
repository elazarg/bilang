join Owner;
yield Owner(minimal: int);
var maxValue: int = minimal;
var Winners: set[role] = {Owner};
var secondMaxValue: int = 0;
join many Bidders;
for yield Bidder(offer: int) from Bidders {
    if (offer == maxValue) {
        add Bidder to Winners;
    } else {
        if (offer > maxValue) { // to make this commutative we'll need >= and collect the set of offers, then select at random
            secondMaxValue := maxValue;
            maxValue := offer;
            Winner := Bidder;
        } else {
            if (offer > secondMaxValue) {
                secondMaxValue := offer;
            }
        }
    }
}
choose from Winners
transfer secondMaxValue from Winner to Owner;


for yield Bidder, max(offer) in Bidder(offer: int) from Bidders groupby offer having min(timestamp) {
    if (offer == maxValue) {
        add Bidder to Winners;
    } else {
        if (offer > maxValue) { // to make this commutative we'll need >= and collect the set of offers, then select at random
            secondMaxValue := maxValue;
            maxValue := offer;
            Winner := Bidder;
        } else {
            if (offer > secondMaxValue) {
                secondMaxValue := offer;
            }
        }
    }
}