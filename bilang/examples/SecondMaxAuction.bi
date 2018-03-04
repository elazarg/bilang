join Owner;

var maxValue: int = Owner.offer;
var Winner: role = Owner;
var secondMaxValue: int = 0;
join many Bidders;
for yield Bidder(offer: int) from Bidders {
    if (offer > maxValue) {
        secondMaxValue := maxValue;
        maxValue := offer;
        Winner := Bidder;
    } else {
        if (offer > secondMaxValue) {
            secondMaxValue := offer;
        }
    }
}
transfer secondMaxValue from Winner to Owner;
