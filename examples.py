#[Example: joint declaration]
class Participant: pass
(a, b) = await (Participant('A'), Participant('B'))
declare("${a} and ${b} are getting married")

#[Example: puzzle]
class A:
    q: int
a = await A

class S:
    m: int; require(m != 1)
    n: int; require(n != 1)
    require(m * n == a.q)
s = await S

declare("${s} solved the problem!")

#[Example: puzzle with payment]
class A:
    amount: money
    q: int
a = await S

class S:
    m: int; require(m != 1)
    n: int; require(n != 1)
    require(m * n == a.q)
s = await S
pay(s, a.amount)

#[Example: trusted simultaneous game]
class Player:
    choice: bool
even, odd = await (Player('Even'), Player('Odd'))
Winner = even if even.choice == odd.choice else odd
declare("${Winner.name} won")

#[Example: simultaneous game]
class Player:
    choice: bool
even, odd = await independent(Player('Even'), Player('Odd'))
Winner = even if even.choice == odd.choice else odd
declare("${Winner.name} won")

#[Example: simultaneous game with payment]
class Player:
    choice: bool
    amount: money; require(amount == 50)
even, odd = await independent(Player('Even'), Player('Odd'))
winner = even if even.choice == odd.choice else odd
pay(winner, even.amount, odd.amount)

#[Example: Binary option / external arbitration]
class Oracle:
    # This is _not_ a commitment, just an acknowledgement of future (value unknown) request
    is_more: future[bool]
class Bet:
    bet: money

oracle = await Oracle(id=0x2346234)
more, less = await (Bet('More'), Bet('Less'))

is_more = await oracle.is_more
winner = more if is_more else less
pay(winner, less.bet, more.bet)

#[Example: Auction]
class Owner:
    minimum: uint

owner = await Owner

last_offer: uint = owner.minimum
while True:
    class Bidder:
        amount: money; require(amount > last_offer)

    # It doesn't behave like a global session here - it's as if there's "Server" and "EveryoneElse"
    # And here the choice is at "EveryoneElse"
    new_bidder = await (RealBidder | Stop(id=owner.id))
    if isinstance(new_bidder, RealBidder):
        transfer(winner, winner.amount)
        winner = new_bidder
        last_offer = len(winner.amount)  # explicit coercion
    else:
        break

pay(owner, winner.amount)

#[Example: Auction without payment and timeouts]
class Owner:
    minimum: money

owner = await Owner

class Bidder:
    pass

bidders: dict[Bidder, future[int]] = {}
while True:
    bidder = await Bidder | Stop(id=owner.id)
    if isinstance(bidder, Bidder):
        bidders.add(bidder)
    else:
        break

last_offer: uint = owner.minimum
winner = NOBODY
async for bidder, bidder.bid in yield from bidders.items():
    # performed lazily
    if bid > last_offer:
        last_offer = bid
        winner = dib.id

declare("${winner} has won")
pay(owner, winner.amount)

#[Example: Monty Hall]
class Host:
    car: future[hidden[int]]
    goat: future[int]

class Guest:
    door1: future[int]
    door2: future[int]

host = await Host
guest = await Guest
with await hidden(host.car):
    await guest.door1
    await host.goat;    require(host.goat != guest.door1)
    await guest.door2;  require(guest.door2 != host.goat)

if host.car is None or host.goat == host.car or guest.door2 == host.car:
    declare("${guest} won")
else:
    declare("${host} won")
