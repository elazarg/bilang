#[Example: joint declaration]
(A, B) = await ([role], [role])
declare("${A} and ${B} are getting married")

#[Example: puzzle]
A = await role
q = await A[int]

class Solution:
    m: int; require(m != 1)
    n: int; require(n != 1)
    require(m * n == a.q)
S = await role
s = await S[Solution]

declare("${s} solved the problem!")

#[Example: puzzle with payment]
A = await role
q = await A[int]
prize = await A[money]
# shorthand: [q, prize] = await role[int, money]

class Solution:
    m: int; require(m != 1)
    n: int; require(n != 1)
    require(m * n == a.q)
S = await role
_ = await S[Solution]
# _ = await role[Solution]
pay(S, prize)

#[Example: simultaneous game]
Even, Odd = await (role, role)
even_choice, odd_choice = await (even[bool], odd[bool])
Winner = even if even_choice == odd_choice else odd
declare("${Winner.name} won")

#[Example: simultaneous game with payment]
Even, Odd = await (role, role)
even_choice, odd_choice = await (even[bool], odd[bool])
Winner = even if even_choice == odd_choice else odd
pay(winner, even.amount, odd.amount)

#[Example: Binary option / external arbitration]
Oracle = await role(id=0x2346234)
[More, bet1], [Less, bet2] = await (role[money], role[money])
is_more = await Oracle[bool]
Winner = <ore if is_more else Less
pay(winner, bet1, bet2)

#[Example: Auction]
Owner = await role

last_offer = await Owner[uint]
while True:
    class Bidder:
        amount: money; require(amount > last_offer)

    # It doesn't behave like a global session here - it's as if there's "Server" and "EveryoneElse"
    # And here the choice is at "EveryoneElse"
    new_bidder = await (role | Stop(id=owner.id))
    if new_bidder.id == owner.id:
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
Host = await role
Guest = await role
with await hidden(Host[int]) as car:
    door1 = await Guest[int]
    goat = await Host[int];  require(goat != door1)
    door1 = await Guest[int];  require(door2 != goat)

if car is None or goat == car or door2 == car:
    declare("${Guest} won")
else:
    declare("${Host} won")
