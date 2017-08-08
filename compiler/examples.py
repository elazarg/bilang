# TODO:
# * TIMEOUT

async def puzzle():
    a = await 'A'
    [q, prize] = await a[int, money]
    require(prize == 80)

    # Race here. Use foreach?
    s = await 'S'
    [m, n] = await s[int, int]
    require(m != 1)
    require(n != 1)
    require(m * n == q)

    pay(s, prize)

async def binary_options():
    oracle = await 'Oracle'
    require(oracle == 0x2346234)
    more, less = await ('More', 'Less')

    is_more = await oracle[bool]
    winner = more if is_more else less
    pay(winner, less.bet, more.bet)


async def trusted_simultaneous_game():
    even, odd = await ('Even', 'Odd')
    ([even_choice, even_amount], [odd_choice, odd_amount]) = await (even[bool, money], odd[bool, money])
    require(even_amount == 50)
    require(odd_amount == 50)
    winner = even if even_choice == odd_choice else odd
    pay(winner, even.amount, odd.amount)

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

'''
async def coin():
    class P: pass
    a, b = await(P, P)
    while True:
        await a
        await b
'''
