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
    address[2] private address_of;

    function stmt_0_join(uint as_role, uint _step_count) step(_step_count) state(0) {
        // Note that a conforming client could execute this function accidentally due to a race condition.
        // This is why we use revert()
        require(as_role == Role_A || as_role == Role_B);
        if (address_of[as_role] != 0x0) revert();

        // Just a thought: putting tx.origin here will give us only external accounts
        // Or we can require(msg.sender == tx.origin)
        address_of[as_role] = msg.sender;

        if (address_of[Role_A] != 0x0 && address_of[Role_B] != 0x0)
            stmt_index++;
    }

    function stmt_1_declare(uint _step_count) step(_step_count) state(1) {
        Declare("${} and ${} are getting married", address_of[Role_A], address_of[Role_B]);
    }

    function end() state(2) {
        selfdestruct(msg.sender);
    }
}

//[Example: puzzle]
contract Puzzle is StateMachine {
    event Declare(string, address, address);
    uint Role_A = 0;
    uint Role_Solver = 1;
    address[2] private address_of;

    int q; address q__sender;
    int m; address m__sender;
    int n; address n__sender;

    function stmt_0_join(uint as_role, uint _step_count) step(_step_count) state(0) {
        require(as_role == Role_A);
        if (address_of[as_role] != 0x0) revert();
        address_of[as_role] = msg.sender;

        if (address_of[Role_A] != 0x0)
            stmt_index++;
    }

    function stmt_1_receive(int _q, uint _step_count) step(_step_count) state(1) {
        require(address_of[Role_A] == msg.sender);
        q = _q;
        q__sender = msg.sender;
    }

    function stmt_2_join(uint as_role, uint _step_count) step(_step_count) state(2) {
        require(as_role == Role_Solver);
        if (address_of[as_role] != 0x0) revert();
        address_of[as_role] = msg.sender;

        if (address_of[Role_Solver] != 0x0)
            stmt_index++;
    }

    function stmt_3_receive(int val0, int val1, uint _step_count) step(_step_count) state(3) {
        if (address_of[Role_Solver] == msg.sender) {
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
    address[2] private address_of;

    bool x; address x__sender;
    bool y; address y__sender;

    function stmt_0_join(uint as_role, uint _step_count) step(_step_count) {
        if (stmt_index != 0) revert();
        
        require(as_role == Role_Even || as_role == Role_Odd);
        if (address_of[as_role] != 0x0) revert();

        address_of[as_role] = msg.sender;

        if (address_of[Role_Even] != 0x0 && address_of[Role_Odd] != 0x0)
            stmt_index++;
    }

    function stmt_1_receive(bool val, uint _step_count) state(1) step(_step_count) {
        require(address_of[Role_Even] == msg.sender);
        if (address_of[Role_Even] == msg.sender) {
            x = val; x__sender = msg.sender;
        } else if (address_of[Role_Odd] == msg.sender) {
            y = val; y__sender = msg.sender;
        } else {
            require(false);
        }
    }

    function stmt_1_declare(uint _step_count) state(2) step(_step_count) {
        if (x == y) {
            Declare("${} won", address_of[Role_Even]);
        } else {
            Declare("${} won", address_of[Role_Odd]);
        }
    }

    function end() state(2) {
        selfdestruct(msg.sender);
    }
}
