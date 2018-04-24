pragma solidity ^0.4.22;
contract Simple {
    constructor() public {
        lastBlock = block.timestamp;
    }
    function keccak(bool x, uint salt) pure public returns(bytes32) {
        return keccak256(x, salt);
    }
    // Step
    uint constant STEP_TIME = 500;
    int step;
    uint lastBlock;
    modifier at_step(int _step) {
        require(step == _step);
        //require(block.timestamp < lastBlock + STEP_TIME);
        _;
    }
    // roles
    enum Role { None, A, B }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
    // step 0
    bool doneA;
    function join_A() at_step(0) public by(Role.None) payable {
        role[msg.sender] = Role.A;
        require(msg.value == 1); 
        require(!doneA);
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneA = true;
    }
    event Broadcast0(); // TODO: add params
    function __nextStep0() public {
        require(step == 0);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast0();
        step = 1;
        lastBlock = block.timestamp;
    }
    // end 0
    // step 1
    bool doneB;
    function join_B() at_step(1) public by(Role.None) payable {
        role[msg.sender] = Role.B;
        require(msg.value == 1); 
        require(!doneB);
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneB = true;
    }
    event Broadcast1(); // TODO: add params
    function __nextStep1() public {
        require(step == 1);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast1();
        step = 2;
        lastBlock = block.timestamp;
    }
    // end 1
    // step 2
    uint A_hidden_c;
    bool A_hidden_c_done;
    bool done_A_2;
    function yield_A2(uint _hidden_c) by (Role.A) at_step(2) public {
        require(!done_A_2);
        require(true);
        A_hidden_c = _hidden_c;
        A_hidden_c_done = true;
        done_A_2 = true;
    }
    event Broadcast2(); // TODO: add params
    function __nextStep2() public {
        require(step == 2);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast2();
        step = 3;
        lastBlock = block.timestamp;
    }
    // end 2
    // step 3
    bool B_c;
    bool B_c_done;
    bool done_B_3;
    function yield_B3(bool _c) by (Role.B) at_step(3) public {
        require(!done_B_3);
        require(true);
        B_c = _c;
        B_c_done = true;
        done_B_3 = true;
    }
    event Broadcast3(); // TODO: add params
    function __nextStep3() public {
        require(step == 3);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast3();
        step = 4;
        lastBlock = block.timestamp;
    }
    // end 3
    // step 4
    bool A_c;
    bool A_c_done;
    bool done_A_4;
    function reveal_A4(bool _c, uint salt) by(Role.A) at_step(4) public {
        require(!done_A_4);
        require(keccak256(_c, salt) == bytes32(A_hidden_c));
        require(true);
        A_c = _c;
        A_c_done = true;
        done_A_4 = true;
    }
    event Broadcast4(); // TODO: add params
    function __nextStep4() public {
        require(step == 4);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast4();
        step = 5;
        lastBlock = block.timestamp;
    }
    // end 4
    function withdraw_5_A() by(Role.A) at_step(5) public {
        int amount;
        amount = ((((A_c != B_c) || ! B_c_done)) ? int(1) : (- int(1)));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_5_B() by(Role.B) at_step(5) public {
        int amount;
        amount = ((((A_c == B_c) || ! A_c_done)) ? int(1) : (- int(1)));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
