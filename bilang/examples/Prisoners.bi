join A();
join B();
yield A(c: bool) B(c: bool);
return (A.c && B.c)
    ? { A -> -10; B -> -10 }
    : (A.c && !B.c) ? { A -> 10; B -> -10 }
    : (!A.c && B.c) ? { A -> 10; B -> -10 }
    : (!A.c && !B.c) ? { A -> 10; B -> 10 }
    : { A -> -100; B -> -100 }
