type choice = {1, 2, 3}

join Issuer() $ 10;
join Alice() $ 10;
join Bob() $ 10;
yield Issuer(c: choice) Alice(c: choice) Bob(c: choice);
withdraw (Alice.c == null || Bob.c == null) ? { Alice -> -10; Bob -> -10; Issuer ->  20 }
: (Issuer.c == null) ?                      { Alice ->  20; Bob -> -10; Issuer -> -10 }
: (Alice.c == Bob.c ) ?                     { Alice -> -10; Bob -> -10; Issuer ->  20 }
: ((Alice.c + Bob.c + Issuer.c) / 2 * 2 == (Alice.c + Bob.c + Issuer.c) ) ?
                                            { Alice ->  20; Bob -> -10; Issuer -> -10 }
:                                           { Alice -> -10; Bob ->  20; Issuer -> -10 }
