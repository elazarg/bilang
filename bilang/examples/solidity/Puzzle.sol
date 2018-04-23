pragma solidity ^0.4.22;
contract Puzzle {
    // roles
    enum Role { None, Q, A }
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
    mapping(address => bytes32) commitsQ;
    mapping(address => uint) timesQ;
    bool halfStepQ;
    function join_commit_Q(bytes32 c) at_step(0) public {
        require(commitsQ[msg.sender] == bytes32(0));
        require(!halfStepQ);
        commitsQ[msg.sender] = c;
        timesQ[msg.sender] = block.timestamp;
    }
    event BroadcastHalfQ();
    function __nextHalfStepQ() at_step(0) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepQ == false);
        emit BroadcastHalfQ();
        halfStepQ = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleQ;
    int Q_x;
    bool Q_x_done;
    function join_Q(int _x, uint salt) at_step(0) public payable {
        require(keccak256(_x, salt) == bytes32(commitsQ[msg.sender]));
        if (chosenRoleQ != address(0x0))
             require(timesQ[msg.sender] < timesQ[chosenRoleQ]);
        role[msg.sender] = Role.Q;
        require(msg.value == 50);
        balanceOf[msg.sender] = msg.value;
        chosenRoleQ = msg.sender;
        require(true);
        Q_x = _x;
        Q_x_done = true;
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
    mapping(address => bytes32) commitsA;
    mapping(address => uint) timesA;
    bool halfStepA;
    function join_commit_A(bytes32 c) at_step(1) public {
        require(commitsA[msg.sender] == bytes32(0));
        require(!halfStepA);
        commitsA[msg.sender] = c;
        timesA[msg.sender] = block.timestamp;
    }
    event BroadcastHalfA();
    function __nextHalfStepA() at_step(1) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepA == false);
        emit BroadcastHalfA();
        halfStepA = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleA;
    int A_p;
    int A_q;
    bool A_p_done;
    bool A_q_done;
    function join_A(int _p, int _q, uint salt) at_step(1) public payable {
        require(keccak256(_p, _q, salt) == bytes32(commitsA[msg.sender]));
        if (chosenRoleA != address(0x0))
             require(timesA[msg.sender] < timesA[chosenRoleA]);
        role[msg.sender] = Role.A;
        require(msg.value == 0);
        balanceOf[msg.sender] = msg.value;
        chosenRoleA = msg.sender;
        require(((_p * _q) == Q_x));
        A_p = _p;
        A_q = _q;
        A_p_done = true;
        A_q_done = true;
    }
    event Broadcast1(); // TODO: add params
    function __nextStep1() at_step(1) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast1();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 1
    function withdraw_2_Q() by(Role.Q) public at_step(2) {
        require(role[msg.sender] == Role.Q);
        int amount;
        amount = int(0);
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_2_A() by(Role.A) public at_step(2) {
        require(role[msg.sender] == Role.A);
        int amount;
        amount = int(50);
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
