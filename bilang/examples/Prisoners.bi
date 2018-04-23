join A();
join B();
yield A(c: bool) B(c: bool); // true means cooperate
return (A.c != null && B.c != null)
?(  (A.c && B.c )   ? { A -> -2; B -> -2 }
    : (A.c && !B.c) ? { A ->  0; B -> -3 }
    : (!A.c && B.c) ? { A -> -3; B ->  0 }
    :                 { A -> -1; B -> -1 }
):(A.c == null) ? { A -> -100; B -> 10 }
:{ A -> 10; B -> -100 }