join Odd;
join Even;
yield Odd(c1: bool) Even(c2: bool);
var Winner : role = (c1 != c2) ? Odd : Even;
transfer Even.value from Even to Winner;
transfer Odd.value from Odd to Winner;
