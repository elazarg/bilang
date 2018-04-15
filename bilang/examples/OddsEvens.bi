receive join Odd()
        join Even()
receive yield  Odd(c: bool)
        yield Even(c: bool)
return (Even.c != undefined && Odd.c != undefined) ?
    ((Even.c == Odd.c) ? { Even -> 10; Odd -> -10 } : { Even -> -10; Odd -> 10 })
: ((Even.c == undefined && Odd.c != undefined) ? { Even -> -100; Odd -> 10 }
: { Even -> -100; Odd -> -100 })

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
