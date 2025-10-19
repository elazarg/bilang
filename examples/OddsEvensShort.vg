join  Odd(c: bool) $ 100
     Even(c: bool) $ 100;
withdraw (Even.c != null && Odd.c != null) ?
            { Even -> ((Even.c <-> Odd.c) ? 10 : -10); Odd -> ((Even.c <-> Odd.c) ? -10 : 10) }
       : (Even.c == null && Odd.c != null) ? { Even -> -100; Odd -> 10 }
       : { Even -> -100; Odd -> -100 }
