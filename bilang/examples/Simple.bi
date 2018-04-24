join A() $ 1;
join B() $ 1;
yield A(c: hidden bool);
yield B(c: bool);
reveal A(c: bool);
return { A -> (A.c != B.c || B.c == null) ? 1 : -1 ;
         B -> (A.c == B.c || A.c == null) ? 1 : -1 }
