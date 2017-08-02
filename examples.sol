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
    uint Role_A = 0;
    uint Role_B = 1;
    address A;
    address B;

    function stmt_0_join(uint as_role, uint _step_count) step(_step_count) state(0) {
        // Note that a conforming client could execute this function accidentally due to a race condition.
        // This is why we use revert()
        require(as_role == Role_A || as_role == Role_B);
        // "Role_A" is the title, "A" is the variable. Here it's the same, but not always.
        if (as_role == Role_A && A != 0x0) revert();
        if (as_role == Role_B && B != 0x0) revert();

        if (as_role == Role_A)
            A = msg.sender;
        if (as_role == Role_B)
            B = msg.sender;

        if (A != 0x0 && B != 0x0)
            stmt_index++;
    }

    function stmt_1_declare(uint _step_count) step(_step_count) state(1) {
        Declare("${} and ${} are getting married", A, B);
    }

    function end() state(2) {
        selfdestruct(msg.sender);
    }
}

//[Example: puzzle]
contract Puzzle is StateMachine {
    event Declare(string, address);
    uint Role_A = 0;
    uint Role_Solver = 1;
    address A;
    address Solver;

    int q; address q__sender;
    int m; address m__sender;
    int n; address n__sender;

    function stmt_0_join(uint as_role, uint _step_count) step(_step_count) state(0) {
        require(as_role == Role_A);
        if (as_role == Role_A && A != 0x0) revert();
        A = msg.sender;

        if (A != 0x0)
            stmt_index++;
    }

    function stmt_1_receive(int _q, uint _step_count) step(_step_count) state(1) {
        require(msg.sender == A);
        q = _q;
        q__sender = msg.sender;
    }

    function stmt_2_join(uint as_role, uint _step_count) step(_step_count) state(2) {
        require(as_role == Role_Solver);
        if (Solver != 0x0) revert();
        Solver = msg.sender;

        if (Solver != 0x0)
            stmt_index++;
    }

    function stmt_3_receive(int val0, int val1, uint _step_count) step(_step_count) state(3) {
        if (Solver == msg.sender) {
            m = val0; m__sender = msg.sender;
            n = val1; n__sender = msg.sender;
        } else {
            require(false);
        }
    }

    function stmt_4_require(uint _step_count) step(_step_count) state_non_inc(4) {
        // Can easily be unified with stmt_3_receive
        if (m != 1 && n != 1 && m * n == q) {
            stmt_index++;
        } else {
            // cleanup is not technically required here
            m = 0; m__sender = 0x0;
            n = 0; n__sender = 0x0;
            stmt_index = 2; // will be ++'ed
        }
    }

    function stmt_5_declare(uint _step_count) step(_step_count) state(5) {
        Declare("${} solved the problem!", Solver);
    }

    function end() {
        require(stmt_index == 6);
        selfdestruct(msg.sender);
    }
}

//[Example: puzzle with payment]
contract PuzzlePayment is StateMachine {
    event Declare(string, address, address);
    uint Role_A = 0;
    uint Role_Solver = 1;
    address A; uint __A_amount;
    address Solver; uint __Solver_amount;
    
    uint[2] private amount_of;

    int q; address q__sender;
    int m; address m__sender;
    int n; address n__sender;

    function stmt_0_join(uint as_role, uint _step_count) step(_step_count) state(0) payable {
        require(as_role == Role_A);
        require(msg.value == 50);
        if (as_role == Role_A && A != 0x0) revert();
        A = msg.sender;

        if (A != 0x0)
            stmt_index++;
    }

    function stmt_1_receive(int _q, uint _step_count) step(_step_count) state(1) {
        require(msg.sender == A);
        q = _q;
        q__sender = msg.sender;
    }

    function stmt_2_join(uint as_role, uint _step_count) step(_step_count) state(2) {
        require(as_role == Role_Solver);
        if (Solver != 0x0) revert();
        Solver = msg.sender;

        if (Solver != 0x0)
            stmt_index++;
    }

    function stmt_3_receive(int val0, int val1, uint _step_count) step(_step_count) state(3) {
        if (Solver == msg.sender) {
            m = val0; m__sender = msg.sender;
            n = val1; n__sender = msg.sender;
        } else {
            require(false);
        }
    }

    function stmt_4_require(uint _step_count) step(_step_count) state_non_inc(4) {
        // Can easily be unified with stmt_3_receive
        if (m != 1 && n != 1 && m * n == q) {
            stmt_index++;
        } else {
            // cleanup is not technically required here
            m = 0; m__sender = 0x0;
            n = 0; n__sender = 0x0;
            stmt_index = 3;
        }
    }

    function stmt_5_pay(uint _step_count) step(_step_count) state(5) {
        //transfer(Solver, __A_amount);
    }

    function end() {
        require(stmt_index == 5);
        selfdestruct(msg.sender);
    }
}

//[Example: trusted simultaneous game]
contract TrustedSimultaneousGame is StateMachine {
    event Declare(string, address);
    uint Role_Even = 0;
    uint Role_Odd = 1;
    address Even;
    address Odd;

    bool x; address x__sender;
    bool y; address y__sender;

    function stmt_0_join(uint as_role, uint _step_count) state(0) step(_step_count) {
        if (as_role == Role_Even && Even != 0x0) revert();
        if (as_role == Role_Odd && Odd != 0x0) revert();

        if (as_role == Role_Even)
            Even = msg.sender;
        if (as_role == Role_Odd)
            Odd = msg.sender;

        if (Even != 0x0 && Odd != 0x0)
            stmt_index++;
    }

    function stmt_1_receive(bool val, uint _step_count) state(1) step(_step_count) {
        if (msg.sender == Even) {
            x = val; x__sender = msg.sender;
        } else if (msg.sender == Odd) {
            y = val; y__sender = msg.sender;
        } else {
            require(false);
        }
    }

    function stmt_2_declare(uint _step_count) state(2) step(_step_count) {
        address Winner = (x == y) ? Even : Odd;
        Declare("${} won", Winner);
    }

    function end() state(2) {
        selfdestruct(msg.sender);
    }
}

//[Example: simultaneous game] -- commitment etc.
//[Example: simultaneous game with payment]

//[Example: Auction without payment; combined]
contract AuctionPayment is StateMachine {
    event Declare(string, address);
    uint Role_Owner = 0;
    uint Role_Bidder = 1;
    address[2] private address_of;

    address Owner = 0x0;
    address Bidder = 0x0;
    address NewBidder = 0x0;
    uint max; address __max_owner;

    function stmt_0_join(uint as_role, uint _step_count) state(0) step(_step_count) {
        require(as_role == Role_Owner);
        if (Owner != 0x0) revert();
        Owner = msg.sender;

        if (Owner != 0x0)
            stmt_index++;
        max = 0;
        Bidder = 0x0;
    }

    function stmt_1_join(uint as_role, uint _step_count) state(0) step(_step_count) payable {
        if (stmt_index != 0) revert();
        
        require(as_role == Role_Bidder);
        // "may_replace=Bidder"
        if (NewBidder != Bidder) revert();
        NewBidder = msg.sender;

        if (NewBidder == Owner) {
            // keep last Bidder
            stmt_index = 3;
            return;
        }
        require(msg.value > max);
        
        if (NewBidder != 0x0)
            stmt_index++;
    }

    function stmt_2_transfer(uint _step_count) state(2) step(_step_count) {
        //LazySend(max, Bidder);
    }

    function stmt_3_assign(uint _step_count) state(3) step(_step_count) {
        Bidder = NewBidder;
    }

    function stmt_4_declare(uint _step_count) state(4) step(_step_count) {
        Declare("${} won", Bidder);
    }

    function end() state(2) {
        selfdestruct(msg.sender);
    }
}
