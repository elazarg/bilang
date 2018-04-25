join  Odd() $ 100;
join Even() $ 100;
yield Odd(c: bool) Even(c: bool);
withdraw (Even.c != null && Odd.c != null) ?
     { Even -> ((Even.c <-> Odd.c) ? 10 : -10); Odd -> ((Even.c <-> Odd.c) ? -10 : 10) }
: (Even.c == null && Odd.c != null) ? { Even -> -100; Odd -> 10 }
: { Even -> -100; Odd -> -100 }
