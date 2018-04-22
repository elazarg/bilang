join A();
join B();
yield A(x: hidden bool);
yield B(y: bool);
reveal A(x: bool);
return { A -> 0; B -> 0 }
