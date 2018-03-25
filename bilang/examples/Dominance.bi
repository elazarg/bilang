join A;
join B;
yield A(c1: bool) B(c2: bool);
var Winner : role = (c1 != c2) ? A : B;
transfer 10 from Even to Odd;
