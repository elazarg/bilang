join many Diners;
var total : int = 0;
var count : int = 0;
for yield Diner(expensive: bool) from Diners where Diner.payment == 100 {
    total := total + expensive ? 100 : 10;
    count := count + 1;
}
var payment: int = total / count;
var rem: int = total - payment * count;
for yield Diner() from Diners {
    transfer payment from This to Diner;
}
