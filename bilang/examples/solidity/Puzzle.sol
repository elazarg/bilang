pragma solidity ^0.4.22;
contract Puzzle {
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
    enum Role { None, Q, A }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
    // step 0
|    mapping(address => bytes32) commitsQ;
|    mapping(address => uint) timesQ;
|    bool halfStepQ;
|
|    function join_commit_Q(bytes32 c) at_step(0) public {
|        require(commitsQ[msg.sender] == bytes32(0));
|        require(!halfStepQ);
|        commitsQ[msg.sender] = c;
|        timesQ[msg.sender] = block.timestamp;
|    }
|
|    event BroadcastHalfQ();
|    function __nextHalfStepQ() at_step(0) public {
|        require(block.timestamp >= lastBlock + STEP_TIME);
|        require(halfStepQ == false);
|        emit BroadcastHalfQ();
|        halfStepQ = true;
|        lastBlock = block.timestamp;
|    }
|
|    
|    int Q_x;
|    bool Q_x_done;
|
|    function join_Q(int _x, uint salt) at_step(0) public payable {
|        require(keccak256(_x, salt) == bytes32(commitsQ[msg.sender]));
|        
|        role[msg.sender] = Role.Q;
|        require(msg.value == 50); 
|        balanceOf[msg.sender] = msg.value;
|        
|        
|        require(true);
|        Q_x = _x;
|        Q_x_done = true;
|    }
|
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
        |    mapping(address => bytes32) commitsA;
        |    mapping(address => uint) timesA;
        |    bool halfStepA;
        |
        |    function join_commit_A(bytes32 c) at_step(1) public {
        |        require(commitsA[msg.sender] == bytes32(0));
        |        require(!halfStepA);
        |        commitsA[msg.sender] = c;
        |        timesA[msg.sender] = block.timestamp;
        |    }
        |
        |    event BroadcastHalfA();
        |    function __nextHalfStepA() at_step(1) public {
        |        require(block.timestamp >= lastBlock + STEP_TIME);
        |        require(halfStepA == false);
        |        emit BroadcastHalfA();
        |        halfStepA = true;
        |        lastBlock = block.timestamp;
        |    }
        |
        |    
        |    int A_p;
int A_q;
        |    bool A_p_done;
bool A_q_done;
        |
        |    function join_A(int _p, int _q, uint salt) at_step(1) public {
        |        require(keccak256(_p, _q, salt) == bytes32(commitsA[msg.sender]));
        |        
        |        role[msg.sender] = Role.A;
        |        
        |        balanceOf[msg.sender] = msg.value;
        |        
        |
        |        require(((((A_p * A_q) == Q_x) && (A_p != int(1))) && (A_q != int(1))));
        |        A_p = _p;
    A_q = _q;
        |        A_p_done = true;
    A_q_done = true;
        |    }
        |
    event Broadcast1(); // TODO: add params
    function __nextStep1() public {
        require(step == 1);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast1();
        step = 2;
        lastBlock = block.timestamp;
    }
    // end 1
    function withdraw_2_Q() by(Role.Q) at_step(2) public {
        int amount;
        amount = int(0);
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_2_A() by(Role.A) at_step(2) public {
        int amount;
        amount = int(50);
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
