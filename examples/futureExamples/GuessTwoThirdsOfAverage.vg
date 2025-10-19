type T = {0..100}

join many PS;
var This: role = 0x0;
var total: int = 0;
var count: int = 0;
for yield P(guess: T) where P.payment == 100
    from PS {
    total := total + guess;
    count := count + 1;
}
var average: int = total / count;
var rem: int = total - average * count;
var winner: role = 0x0;
var closest: int = 1000;
var closest_time: int = 1000;
for yield P() from PS {
    var current: int = abs(P.guess - average);
    var current_time: int = 0; //timestamp(P.guess);
    if (current < closest) {
        closest := current;
        closest_time := current_time;
        winner := P;
    }
}
transfer _ from This to winner;
