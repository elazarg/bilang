type choice = {1, 2, 3}

join Issuer(c: choice) $ 10
     Alice(c: choice) $ 10
     Bob(c: choice) $ 10;

return (Alice.c  == null || Bob.c == null)
             ? { Alice -> -10; Bob -> -10; Issuer ->  20 }
      : (Issuer.c == null)
             ? { Alice ->  20; Bob -> -10; Issuer -> -10 }
      : ((Issuer.c + Alice.c + Bob.c) / 3 * 3 == (Issuer.c + Alice.c + Bob.c))
             ? { Alice ->  20; Bob -> -10; Issuer -> -10 }
      : ((Issuer.c + Alice.c + Bob.c) / 3 * 3 == (Issuer.c + Alice.c + Bob.c)-1)
             ? { Alice -> -10; Bob ->  20; Issuer -> -10 }
      :        { Alice -> -10; Bob -> -10; Issuer ->  20 }
