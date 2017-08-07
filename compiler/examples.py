# TODO:
# * abstract syntax
# * infer
# * TIMEOUT

async def puzzle():
    class A:
        q: int
        price: money
        require(price == 80)
    a = await A

    class S:
        m: int; require(m != 1)
        n: int; require(n != 1)
        require(m * n == a.q)

    # Race here
    s = await S

    pay(s, a.price)

'''
async def safe_puzzle():
    class A:
        q: int
        price: money
        require(price == 80)
    a = await A

    class S:
        m: hidden[int]; require(m != 1)
        n: hidden[int]; require(n != 1)
        require(m * n == a.q)
    
    while True:
        s = await initialized_timeout(S)
        if s.timeout:
            pay(a, s.penalty)
            discharge(s)
        else:
            pay(s, a.price, s.penalty)
            return
'''

async def binary_options():
    class Oracle:
        # This is _not_ a commitment, just an acknowledgement of future (value unknown) request
        is_more: future[bool]

    class Bet:
        bet: money
        require(bet == 100)
    
    oracle = await Oracle
    require(oracle == 0x2346234)
    more, less = await (Bet('More'), Bet('Less'))
    
    await oracle.is_more
    winner: Bet = more if oracle.is_more else less
    pay(winner, less.bet, more.bet)


async def trusted_simultaneous_game():
    class Player:
        choice: future[bool]
        amount: money; require(amount == 50)
    even, odd = await (Player('Even'), Player('Odd'))
    await (even.choice, odd.choice)
    winner: Player = even if even.choice == odd.choice else odd
    pay(winner, even.amount, odd.amount)

'''
async def coin():
    class P: pass
    a, b = await(P, P)
    while True:
        await a
        await b
'''
