join  Odd(c: bool) join Even(c: bool);
return (Even.c != null && Odd.c != null) ?
    let p: int = ((Even.c == Odd.c) ? 10 : -10) in { Even -> p; Odd -> -p }
: (Even.c == null && Odd.c != null) ? { Even -> -100; Odd -> 10 }
: { Even -> -100; Odd -> -100 }
