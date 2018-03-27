join Odd;
join Even;
yield Odd(c1: bool) Even(c2: bool);
if (c1 != undefined && c2 != undefined) {
    if (c1 != c2) {
        transfer 10 from Even to Odd;
    } else {
        transfer 10 from Odd to Even;
    }
} else if (c2 == undefined) {
    transfer 10 from Even to Odd;
} else {
    transfer 10 from Odd to Even;
}
/*

phi_Odd =

exists c1, forall c2,  // yield Odd(c1: bool) Even(c2: bool);
     (c1 == c2) /\ W_EVEN = -10 /\ W_ODD == 10
 \/ !(c1 == c2) /\ W_ODD = -10 /\  W_EVEN == 10

exists c, forall c1, forall c2,
       ((c == c2)  /\ W_EVEN = -10  /\ W_ODD == 10
    \/ !(c == c2)  /\ W_ODD = -10   /\ W_EVEN == 10)
 /\   ((c1 == c2)  /\ W_EVEN1 = -10 /\ W_ODD1 == 10
    \/ !(c1 == c2) /\ W_ODD1 = -10  /\ W_EVEN1 == 10)
 -> W_ODD >= W_ODD1

*/
