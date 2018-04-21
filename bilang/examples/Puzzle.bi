join Q(x: int);
join A(p: int, q: int) where p * q == x;
return {
    Q -> 0;
    A -> 50;
}
