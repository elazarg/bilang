pragma solidity ^0.4.22;
contract Simple {
    // roles
    enum Role { None, A, B }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
    // Step
    uint constant STEP_TIME = 500;
    int step;
    uint __lastStep;
    modifier at_step(int _step) {
        require(step == _step);
        require(block.timestamp < __lastStep + STEP_TIME);
        _;
    }
    // step 0
    mapping(address => bytes32) commitsA;
    mapping(address => uint) timesA;
    bool halfStepA;
    function join_commit_A(bytes32 c) at_step(0) public {
        require(commitsA[msg.sender] == bytes32(0));
        require(!halfStepA);
        commitsA[msg.sender] = c;
        timesA[msg.sender] = block.timestamp;
    }
    event BroadcastHalfA();
    function __nextHalfStepA() at_step(0) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepA == false);
        emit BroadcastHalfA();
        halfStepA = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleA;
    function join_A(uint salt) at_step(0) public payable {
        require(keccak256(salt) == bytes32(commitsA[msg.sender]));
        if (chosenRoleA != address(0x0))
             require(timesA[msg.sender] < timesA[chosenRoleA]);
        role[msg.sender] = Role.A;
        balanceOf[msg.sender] = msg.value;
        chosenRoleA = msg.sender;
        require(true);
    }
    event Broadcast0(); // TODO: add params
    function __nextStep0() at_step(0) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast0();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 0
    // step 1
    mapping(address => bytes32) commitsB;
    mapping(address => uint) timesB;
    bool halfStepB;
    function join_commit_B(bytes32 c) at_step(1) public {
        require(commitsB[msg.sender] == bytes32(0));
        require(!halfStepB);
        commitsB[msg.sender] = c;
        timesB[msg.sender] = block.timestamp;
    }
    event BroadcastHalfB();
    function __nextHalfStepB() at_step(1) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepB == false);
        emit BroadcastHalfB();
        halfStepB = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleB;
    function join_B(uint salt) at_step(1) public payable {
        require(keccak256(salt) == bytes32(commitsB[msg.sender]));
        if (chosenRoleB != address(0x0))
             require(timesB[msg.sender] < timesB[chosenRoleB]);
        role[msg.sender] = Role.B;
        balanceOf[msg.sender] = msg.value;
        chosenRoleB = msg.sender;
        require(true);
    }
    event Broadcast1(); // TODO: add params
    function __nextStep1() at_step(1) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast1();
        step += 1;
        __lastStep = block.timestamp;
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
    function __nextStep2() at_step(2) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast2();
        step += 1;
        __lastStep = block.timestamp;
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
    function __nextStep3() at_step(3) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast3();
        step += 1;
        __lastStep = block.timestamp;
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
    function __nextStep4() at_step(4) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast4();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 4
}
