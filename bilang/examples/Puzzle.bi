join Q(x: int) $ 50;
join A(p: int, q: int) where A.p * A.q == Q.x && A.p != 1 && A.q != 1; // not checking that they are prime
return {
    Q -> 0;
    A -> 50;
}
