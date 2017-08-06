async def puzzle():
    class A:
        q: int
        price: money
    a = await A

    class S:
        m: int; require(m != 1)
        n: int; require(n != 1)
        require(m * n == a.q)

    # Race here
    s = await S

    pay(a.price, s)


async def binary_options():
    class Oracle:
        # This is _not_ a commitment, just an acknowledgement of future (value unknown) request
        is_more: future[bool]

    class Bet:
        bet: money
    
    oracle = await Oracle
    require(oracle == 0x2346234)
    more, less = await (Bet('More'), Bet('Less'))
    
    await oracle.is_more
    winner: address = more if oracle.is_more else less
    pay(winner, less.bet, more.bet)


async def trusted_simultaneous_game():
    class Player:
        choice: bool
        amount: money; require(amount == 50)
    even, odd = await (Player('Even'), Player('Odd'))
    winner: Player = even if even.choice == odd.choice else odd
    pay(winner, even.amount, odd.amount)
