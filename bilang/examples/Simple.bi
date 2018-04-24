join A() $ 1;
join B() $ 1;
yield A(x: hidden bool);
yield B(y: bool);
reveal A(x: bool);
return { A -> (A.x != B.y || B.y == null) 1 : -1 ;
         B -> (A.x == B.y || A.y == null) 1 : -1 }
