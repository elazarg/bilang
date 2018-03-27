type choice = {1, 2, 3}

join Issuer;
join Alice;
join Bob;
yield Issuer(c1: choice) Alice(c2: choice) Bob(c3: choice);
var Winner : role = 0x0;
if (c2 == undefined || c3 == undefined) {
    Winner := Issuer;
} else {
    if (c1 == undefined) {
        Winner := Alice;
    } else {
        var sum : int = c1 + c2 + c3;
        var s1 : int = sum / 3 * 3;
        Winner := (s1 == sum) ? Alice : ((s1 == sum-1) ? Bob : Issuer);
    }
}
transfer 10 from Alice to Winner;
transfer 10 from Bob to Winner;
transfer 10 from Issuer to Winner;