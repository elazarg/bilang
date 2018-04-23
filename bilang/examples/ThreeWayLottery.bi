type choice = {1, 2, 3}

join Issuer();
join Alice();
join Bob();
yield Issuer(c: choice) Alice(c: choice) Bob(c: choice);

return (Alice.c  == null || Bob.c == null)
            ? { Alice -> -10; Bob -> -10; Issuer ->  20 }
     : (Issuer.c == null)
            ? { Alice ->  20; Bob -> -10; Issuer -> -10 }
     : ((Issuer.c + Alice.c + Bob.c) / 3 * 3 == (Issuer.c + Alice.c + Bob.c))
            ? { Alice ->  20; Bob -> -10; Issuer -> -10 }
     : ((Issuer.c + Alice.c + Bob.c) / 3 * 3 == (Issuer.c + Alice.c + Bob.c)-1)
            ? { Alice -> -10; Bob ->  20; Issuer -> -10 }
     :        { Alice -> -10; Bob -> -10; Issuer ->  20 }
