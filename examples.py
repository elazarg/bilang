#[Example: joint declaration]
(A, B) = join('A'), join('B')
declare("${A.id} and ${B.id} are getting married")

#[Example: puzzle]
A = join('A')
q = receive[int] @ A
# (The above could be performed locally)
B = join('Solver')
m, n = receive[int] @ B  # doing it in 2 statements leads to ambiguity about where to backtrack
require(m != 1 && n != 1 && m * n == q)
declare("${Solver.name} solved the problem!")

#[Example: puzzle with payment]
A = join('A', money=50)
q = receive[int] @ A
B = join('Solver')
m, n = receive[int] @ B  # doing it in 2 statements leads to ambiguity about where to backtrack
require(m != 1 && n != 1 && m * n == q)
pay(B, A.money)

#[Example: trusted simultaneous game]
Even, Odd = join('Even'), join('Odd')
x, y = receive[bool] @ Even, receive[bool] @ Odd  # We could call the variable Even.x to be explicit
Winner = Even if x == y else Odd
declare("${Winner.name} won")

#[Example: simultaneous game]
Even, Odd = join('Even', 'Odd')
x, y = receive_independent[bool] @ (Even, Odd)
Winner = Even if x == y else Odd
declare("${Winner.name} won")

#[Example: simultaneous game with payment]
Even, Odd = join('Even', money=50), join('Odd', money=50)
x, y = receive_independent[bool] @ (Even, Odd)
Winner = Even if x == y else Odd
pay(Winner, Even.money, Odd.money)

#[Example: Binary option / external arbitration]
Oracle = join(0x2346234)
More, Less = join('More', money=50), join('More', money=50)

is_more = receive[bool] @ Oracle
Winner : Role = More if is_more else Less
pay(Winner, Less.money, More.money)

#[Example: Auction without payment; combined]
Owner = join('Owner')
max = 0
Bidder = NOBODY
while True:
    NewBidder = join('Bidder', may_replace=Bidder)
    if NewBidder == Owner:
        break
    require(Bidder.money > max)
    transfer(Bidder.money, Bidder)
    Bidder = NewBidder

declare("${Bidder.name} has won")

#[Example: Auction without payment and timeouts]
Bidders = []
while True:
    Bidder = join('Bidder')
    if Bidder == 0x12874632:
        break
    Bidders.append(Bidder)

max = 0
Bidder = NOBODY
for bid in receive(int) @ Bidders: # performed lazily
    if bid > max:
        max = bid
        Bidder = dib.id

declare("${Bidder.name} has won")

#[Example: Blind auction without payment and timeouts]
Bidders = []
while True:
    Bidder = join('Bidder')
    if Bidder == 0x12874632:
        break
    Bidders.append()

max = 0
Bidder = NOBODY
for bid in receive_independent[int] @ Bidders:   # should be performed lazily, on the reveal
    if bid > max:
        max = bid
        Bidder = dib.id

declare("${Bidder.name} has won")

#[Example: Monty Hall]
Host, Guest = join('Host', 'Guest')
with hidden[int]('car') @ Host as car:
    # `car` value is unusabe inside this block
    door1 = receive[int] @ Guest
    goat = receive[int] @ Host;    require(goat != door1)
    door2 = receive[int] @ Guest;  require(door2 != goat)

require(goat != car)  # should blame host, since he owns both values. This is simple taint tracking, but is inferrable at compile time and can be made explicit
Winner = Guest if if door2 == car else Host
declare("${Winner.name} won")
