pragma solidity ^0.4.22;
contract Simple {
    constructor() public {
        lastBlock = block.timestamp;
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
    function join_A() at_step(0) public payable {
        role[msg.sender] = Role.A;
        require(msg.value == 0);
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
    function join_B() at_step(1) public payable {
        role[msg.sender] = Role.B;
        require(msg.value == 0);
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
    uint A_hidden_x;
    bool A_hidden_x_done;
    bool done_A_2;
    function yield_A2(uint _hidden_x) at_step(2) public {
        require(role[msg.sender] == Role.A);
        require(!done_A_2);
        require(true);
        A_hidden_x = _hidden_x;
        A_hidden_x_done = true;
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
    bool B_y;
    bool B_y_done;
    bool done_B_3;
    function yield_B3(bool _y) at_step(3) public {
        require(role[msg.sender] == Role.B);
        require(!done_B_3);
        require(true);
        B_y = _y;
        B_y_done = true;
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
    bool A_x;
    bool A_x_done;
    bool done_A_4;
    function reveal_A4(bool _x, uint salt) at_step(4) public {
        require(role[msg.sender] == Role.A);
        require(!done_A_4);
        require(keccak256(_x, salt) == bytes32(A_hidden_x));
        require(true);
        A_x = _x;
        A_x_done = true;
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
    function withdraw_5_A() by(Role.A) public at_step(5) {
        require(role[msg.sender] == Role.A);
        int amount;
        amount = int(0);
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_5_B() by(Role.B) public at_step(5) {
        require(role[msg.sender] == Role.B);
        int amount;
        amount = int(0);
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }

    function kecccak(bool x, uint salt) constant public {
        return keccak256(x, salt);
    }
}
