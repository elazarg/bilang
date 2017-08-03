#[Example: joint declaration]
class A: ...
class B: ...
(a, b) = yield {A, B}
declare("${A.id} and ${B.id} are getting married")

#[Example: puzzle]
class A:
    q: int
a = yield A

class S:
    m: int; require(m != 1)
    n: int; require(n != 1)
    require(m * n == a.q)
s = yield S

declare("${s} solved the problem!")

#[Example: puzzle with payment]
class A:
    amount: money
    q: int
a = yield S

class Solver:
    m: int; require(m != 1)
    n: int; require(n != 1)
    require(m * n == a.q)
s = yield S
pay(s, a.amount)

#[Example: trusted simultaneous game]
class Player:
    choice: bool
even, odd = yield {Player('Even'), Player('Odd')}
Winner = even if even.choice == odd.choice else odd
declare("${Winner.name} won")

#[Example: simultaneous game]
class Player:
    choice: bool
even, odd = independent(yield {Player('Even'), Player('Odd')})
Winner = even if even.choice == odd.choice else odd
declare("${Winner.name} won")

#[Example: simultaneous game with payment]
class Player:
    choice: bool
    amount: money; require(amount == 50)
even, odd = yield independent(Player('Even'), Player('Odd'))
winner = even if even.choice == odd.choice else odd
pay(winner, even.money, odd.money)

#[Example: Binary option / external arbitration]
class Oracle:
    # This is _not_ a commitment, just an acknowledgement of future (value unknown) request
    is_more: future[bool]
class Bet:
    bet: money

oracle = yield Oracle(id=0x2346234)
with parallel:
    more, less = yield (Bet('More'), Bet('Less'))

is_more = yield oracle.is_more
winner = more if is_more else less
pay(winner, less.bet, more.bet)

#[Example: Auction without payment; combined]
class Owner:
    minimum: money

owner = yield Owner

last_offer : int = Owner.minimum
while True:
    class Bidder:
        amount: money; require(amount > last_offer)

    new_bidder = yield (RealBidder | Stop(id=owner.id))
    if isinstance(new_bidder, RealBidder):
        transfer(winner, winner.amount)
        winner = new_bidder
        last_offer = len(winner.amount)  # explicit coercion
    else:
        break

declare("${winner.name} has won")
pay(owner, winner.amount)

#[Example: Auction without payment and timeouts]
class Owner:
    minimum: money

owner = yield Owner

class Bidder:
    bid: future[hidden[int]]

bidders = set()
while True:
    bidder = yield Bidder | Stop(id=owner.id)
    if isinstance(bidder, Bidder):
        bidders.add(bidder)
    else:
        break

max = 0
winner = NOBODY
for bidder, bid in independent(yield from {(b, b.bid) for b in bidders}):
    # performed lazily
    if bid > max:
        max = bid
        winner = dib.id

declare("${winner} has won")
pay(owner, winner.amount)

#[Example: Monty Hall]
class Host:
    car: future[hidden[int]]
    goat: future[int]

class Guest:
    door1: int
    door2: future[int]

host = yield Host
guest = yield Guest
with yield hidden(host.car):
    yield host.goat; require(host.goat != guest.door1)
    yield guest.door2;  require(guest.door2 != host.goat)

require(host.goat != host.car)
winner = guest if if door2 == car else host
declare("${winner} won")
