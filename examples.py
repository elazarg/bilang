#[Example: joint declaration]
(A, B) = join('A', 'B')
declare("${A.id} and ${B.id} are getting married")

#[Example: puzzle]
A = join('A')
q = receive[int] @ A
# (The above could be performed locally)
B = join('Solver')
m, n = receive[int] @ B  # doing it in 2 statements leads to ambiguity about where to backtrack
require(m * n == q)
declare("${B.name} solved the problem!")

#[Example: trusted simultaneous game]
Even, Odd = join('Even', 'Odd')
x, y = receive[bool] @ (Even, Odd)  # We could call the variable Even.x to be explicit
if x == y:
    declare("${Even.name} won")
else:
    declare("${Odd.name} won")

#[Example: simultaneous game]
Even, Odd = join('Even', 'Odd')
x, y = receive_independent[bool] @ (Even, Odd)
if x == y:
    declare("${Even.name} won")
else:
    declare("${Odd.name} won")

#[Example: simultaneous game with payment]
Even, Odd = join('Even', 'Odd')
x, y = receive_independent[bool] @ (Even, Odd)
if x == y:
    pay(Even, 100)
else:
    pay(Odd, 100)

#[Example: Binary option / external arbitration]
Oracle = join(0x2346234)
More, Less = join('More', 'Less')
is_more = receive[bool] @ Oracle
if is_more:
    pay(More, 100)
else:
    pay(Less, 100)

#[Example: Auction without payment and timeouts]
Bidders = join_many('Bidder')  # Bidders is an array of length > 0
max = 0
Bidder = NOBODY
for bid in receive(int) @ Bidders: # performed lazily
    if bid > max:
        max = bid
        Bidder = dib.id

declare("${B.name} has won")

#[Example: Blind auction without payment and timeouts]
Bidders = join_many('Bidder')
max = 0
Bidder = NOBODY
for bid in receive_independent[int] @ Bidders:   # should be performed lazily, on the reveal
    if bid > max:
        max = bid
        Bidder = dib.id

declare("${B.name} has won")

#[Example: Monty Hall]
Host, Guest = join('Host', 'Guest')
with hidden[int]('car') @ Host as car:
    # `car` value is unusabe inside this block
    door1 = receive[int] @ Guest
    goat = receive[int] @ Host;    require(goat != door1)
    door2 = receive[int] @ Guest;  require(door2 != goat)

require(goat != car)  # should blame host, since he owns both values. This is simple taint tracking, but is inferrable at compile time and can be made explicit
if door2 == car:
    declare("${Guest.name} won")
else:
    declare("${Host.name} won")
