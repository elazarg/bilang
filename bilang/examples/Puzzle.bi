join Q(x: int) $ 50;
join A(p: int, q: int) where p * q == Q.x;
return {
    Q -> 0;
    A -> 50;
}
