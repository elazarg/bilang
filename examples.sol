pragma solidity ^0.4.14;

contract StateMachine {
    uint stmt_index = 0;
    
    /// step count is nonce, strictly increasing - but not between parallel operations
    /// so this is race-avoiding identity of state-instance on the trace
    /// It will also never overflow... :)
    uint step_count = 0;

    modifier step(uint _step_count) {
        if (step_count != _step_count) revert();
        _;
        step_count++;
    }
    
    modifier state(uint s) {
        if (s != stmt_index) revert();
        _;
        stmt_index++;
    }
    
    modifier state_non_inc(uint s) {
        if (s != stmt_index) revert();
        _;
    }
}

//[Example: joint declaration]
contract JointDeclaration is StateMachine {
    event Declare(string, address, address);
    address a;
    address b;

    // (a, b) = await {A, B}
    function stmt_0_await_A(uint _step_count) step(_step_count) state_non_inc(0) {
        if (a != 0x0) revert();
        a = msg.sender;
        inc_if_finish();
    }
    
    // (a, b) = await {A, B}
    function stmt_0_await_B(uint _step_count) step(_step_count) state_non_inc(0) {
        if (b != 0x0) revert();
        b = msg.sender;
        inc_if_finish();
    }

    function inc_if_finish() internal {
        if (a != 0x0 && b != 0x0) {
            step_count++;
            stmt_index++;
        }
    }

    // declare("${A.id} and ${B.id} are getting married")
    function stmt_1_declare(uint _step_count) step(_step_count) state(1) {
        Declare("${} and ${} are getting married", a, b);
    }

    function end() state(2) {
        selfdestruct(msg.sender);
    }
}

//[Example: puzzle]
contract Puzzle is StateMachine {
    event Declare(string, address);
    address a;
    int a__q;

    address s;
    int s__m;
    int s__n;

    // a = await A [A has q: int]
    function stmt_0_await_A(int q, uint _step_count) step(_step_count) state(0) {
        if (a != 0x0) revert();
        a = msg.sender;
        a__q = q;
    }
    
    // s = await S
    function stmt_1_await_S(int m, int n,  uint _step_count) step(_step_count) state(1) {
        s = msg.sender;
        require(m != 1);  s__m = m;
        require(n != 1);  s__n = n;
        require(m * n == a__q);
    }

    function stmt_2_declare(uint _step_count) step(_step_count) state(2) {
        Declare("${} solved the problem!", Solver);
    }

    function end() state(3) {
        selfdestruct(msg.sender);
    }
}

//[Example: puzzle with payment]
contract PuzzlePayment is StateMachine {
    event Declare(string, address);
    address a;
    int a__q;
    int a__amount;

    address s;
    int s__m;
    int s__n;

    // a = await A [A has q: int]
    function stmt_0_await_A(int q, uint _step_count) step(_step_count) state(0) payable {
        a = msg.sender;
        a__amount = msg.value;
        a__q = q;
    }
    
    // s = await S
    function stmt_1_await_S(int m, int n,  uint _step_count) step(_step_count) state(1) {
        s = msg.sender;
        require(m != 1);  s__m = m;
        require(n != 1);  s__n = n;
        require(m * n == a__q);
    }

    function stmt_2_pay(uint _step_count) step(_step_count) state(2) {
        //transfer(s, a__amount);
    }

    function end() state(3) {
        selfdestruct(msg.sender);
    }
}

//[Example: trusted simultaneous game]
contract TrustedSimultaneousGame is StateMachine {
    event Declare(string, address);
    address even;
    bool even__choice;

    address odd;
    bool odd__choice;

    address winner;

    function state_0_await_Even(bool choice, uint _step_count) {
        require(_step_count == step_count);
        require(state == 0);
        if (even != 0x0) revert();
        
        even = msg.sender;
        
        even__choice = choice; 
        
        if (even != 0x0 && odd != 0x0) {
            step_count += 1;
            state = 1;
        }
    }

    function state_0_await_Odd(bool choice, uint _step_count) {
        require(_step_count == step_count);
        require(state == 0);
        if (odd != 0x0) revert();
        
        odd = msg.sender;
        
        odd__choice = choice; 
        
        if (even != 0x0 && odd != 0x0) {
            step_count += 1;
            state = 1;
        }
    }

    function stmt_1_declare(uint _step_count) state(1) step(_step_count) {
        winner = (even__choice == odd__choice) ? even : odd;
        Declare("${} won", winner);
    }

    function end() state(2) {
        selfdestruct(msg.sender);
    }
}

//[Example: simultaneous game] -- commitment etc.
//[Example: simultaneous game with payment]

//[Example: Monty Hall]
contract MontyHall is StateMachine {
    event Declare(string, address);
    address host;
    bytes64 host__car__commit;
    int host__car;
    bool host__car__failed; // ad-hoc option type
    int host__goat;

    address guest;
    int guest__door1;
    int guest__door2;

    // host = await Host
    function stmt_0_await_Host(uint _step_count) step(_step_count) state(0) payable {
        host = msg.sender;
        host__amount = msg.value;
    }
    
    // guest = await Guest
    function stmt_1_await_Guest(uint _step_count) step(_step_count) state(1) {
        guest = msg.sender;
    }

    // with await hidden(host.car):
    function stmt_2_with_await_hidden(int host__car__commit, uint _step_count) by(host) step(_step_count) state(2) {
        host__car__commit = car__commit;
    }

    // await guest.door1
    function stmt_3_await_door1(int door1, uint _step_count) by(guest) step(_step_count) state(3) {
        guest__door1 = door1;
    }

    // await host.goat; require(host.goat != guest.door1)
    function stmt_4_await_goat(int goat, uint _step_count) by(host) step(_step_count) state(4) {
        require(goat != guest__door1);
        host__goat = goat;
    }

    // await guest.door2;  require(guest.door2 != host.goat)
    function stmt_5_await_door1(int door2, uint _step_count) by(guest) step(_step_count) state(5) {
        require(door2 != gost__goat);
        guest__door2 = door2;
    }

    // EXIT with await hidden(host.car)
    function stmt_6_with_await_hidden(int car, uint salt, uint _step_count) by(host) step(_step_count) state(6) {
        host__car__failed = sha3(car, salt) != host__car__commit);
        if (!host__car__failed)
            host__car = car;
    }

    function stmt_7_declare(uint _step_count) step(_step_count) state(7) {
        if (host__car__failed || host__goat == host__car || guest__door2 == host__car)
            Declare("${} won", guest);
        else
            Declare("${} won", host);
    }

    function end() state(8) {
        selfdestruct(msg.sender);
    }
}

//[Example: Auction]
contract Auction is StateMachine {
    event Declare(string, address);
    address owner = 0x0;
    uint owner__minimum;

    uint last_offer;

    address winner = 0x0;

    function stmt_0_await_Owner(uint minimum, uint _step_count) state(0) step(_step_count) {
        owner = msg.sender;
        owner__minimum = minimum;

        //combined - pure optimization?
        last_offer = owner__minimum;
    }

    function stmt_1_await_Bidder(uint _step_count) state(1) step(_step_count) payable {
        // isinstance is in the method name?
        require(msg.value > last_offer);
        lazy_transfer(winner, winner.amount);
        last_offer = winner.amount;  // implicit coercion :(
        winner = msg.sender;
    }

    function stmt_1_await_Stop(uint _step_count) state(1) step(_step_count) payable {
        require(msg.address == owner);
        // break 
        stmt_index = 3;
    }

    function stmt_4_pay(uint _step_count) state(2) step(_step_count) {
        transfer(bidder, winner.amount);
        // no price yet
    }

    function end() state(2) {
        selfdestruct(msg.sender);
    }
}
