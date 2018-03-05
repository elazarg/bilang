type T = {0..100}

join many PS;
var total: int = 0;
var count: int = 0;
for yield P(guess: T) from PS where P.payment == 100 {
    total := total + guess;
    count := count + 1;
}
var average: int = total / count;
var rem: int = total - payment * count;
var winner: address = None;
var closest: int = 1000;
var closest_time: int = 1000;
for yield P() from PS {
    var current: int = abs(P.guess - average);
    var current_time: int = timestamp(P.guess);
    if (current < closest) {
        closest := current;
        closest_time := current_time;
        winner := P.address;
    }
}
transfer _ from This to winner;
