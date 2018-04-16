type choice = {1, 2, 3}

join Issuer();
join Alice();
join Bob();
yield Issuer(c: choice) yield Alice(c: choice) yield Bob(c: choice);

return (Alice.c  == null || Bob.c == null)
            ? { Alice -> -10; Bob -> -10; Issuer ->  20 }
     : (Issuer.c == null)
            ? { Alice ->  20; Bob -> -10; Issuer -> -10 }
     : let sum : int = Issuer.c + Alice.c + Bob.c in
       let s1 : int = sum / 3 * 3 in
       (s1 == sum)
            ? { Alice ->  20; Bob -> -10; Issuer -> -10 }
     : (s1 == sum-1)
            ? { Alice -> -10; Bob ->  20; Issuer -> -10 }
     :        { Alice -> -10; Bob -> -10; Issuer ->  20 }
