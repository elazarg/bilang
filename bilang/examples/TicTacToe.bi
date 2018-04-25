type d = {0, 1, 2, 3, 4, 5, 6, 7, 8}

join X() $ 100;
join O() $ 100;
yield X(c1: d) where alldiff(X.c1);
yield O(c1: d) where alldiff(X.c1, O.c1);
yield X(c2: d) where alldiff(X.c1, O.c1, X.c2);
yield O(c2: d) where alldiff(X.c1, O.c1, X.c2, O.c2);
yield X(c3: d) where alldiff(X.c1, O.c1, X.c2, O.c2, X.c3);
yield O(c3: d) where alldiff(X.c1, O.c1, X.c2, O.c2, X.c3, O.c3);
yield X(c4: d) where alldiff(X.c1, O.c1, X.c2, O.c2, X.c3, O.c3, X.c4);
yield O(c4: d) where alldiff(X.c1, O.c1, X.c2, O.c2, X.c3, O.c3, X.c4, O.c4);
withdraw { X -> 0; O -> 0 }
