pragma solidity ^0.4.22;
contract OddsEvensShort {
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
    enum Role { None, Odd, Even }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
    // step 0
|    mapping(address => bytes32) commitsOdd;
|    mapping(address => uint) timesOdd;
|    bool halfStepOdd;
|
|    function join_commit_Odd(bytes32 c) at_step(0) public {
|        require(commitsOdd[msg.sender] == bytes32(0));
|        require(!halfStepOdd);
|        commitsOdd[msg.sender] = c;
|        timesOdd[msg.sender] = block.timestamp;
|    }
|
|    event BroadcastHalfOdd();
|    function __nextHalfStepOdd() at_step(0) public {
|        require(block.timestamp >= lastBlock + STEP_TIME);
|        require(halfStepOdd == false);
|        emit BroadcastHalfOdd();
|        halfStepOdd = true;
|        lastBlock = block.timestamp;
|    }
|
|    
|    bool Odd_c;
|    bool Odd_c_done;
|
|    function join_Odd(bool _c, uint salt) at_step(0) public payable {
|        require(keccak256(_c, salt) == bytes32(commitsOdd[msg.sender]));
|        
|        role[msg.sender] = Role.Odd;
|        require(msg.value == 100); 
|        balanceOf[msg.sender] = msg.value;
|        
|        
|        require(true);
|        Odd_c = _c;
|        Odd_c_done = true;
|    }
|
|    mapping(address => bytes32) commitsEven;
|    mapping(address => uint) timesEven;
|    bool halfStepEven;
|
|    function join_commit_Even(bytes32 c) at_step(0) public {
|        require(commitsEven[msg.sender] == bytes32(0));
|        require(!halfStepEven);
|        commitsEven[msg.sender] = c;
|        timesEven[msg.sender] = block.timestamp;
|    }
|
|    event BroadcastHalfEven();
|    function __nextHalfStepEven() at_step(0) public {
|        require(block.timestamp >= lastBlock + STEP_TIME);
|        require(halfStepEven == false);
|        emit BroadcastHalfEven();
|        halfStepEven = true;
|        lastBlock = block.timestamp;
|    }
|
|    
|    bool Even_c;
|    bool Even_c_done;
|
|    function join_Even(bool _c, uint salt) at_step(0) public payable {
|        require(keccak256(_c, salt) == bytes32(commitsEven[msg.sender]));
|        
|        role[msg.sender] = Role.Even;
|        require(msg.value == 100); 
|        balanceOf[msg.sender] = msg.value;
|        
|        
|        require(true);
|        Even_c = _c;
|        Even_c_done = true;
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
    function withdraw_1_Even() by(Role.Even) at_step(1) public {
        int amount;
        amount = ((((! ! Even_c_done) && (! ! Odd_c_done))) ? (((Even_c == Odd_c)) ? int(10) : (- int(10))) : (((! Even_c_done && (! ! Odd_c_done))) ? (- int(100)) : (- int(100))));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_1_Odd() by(Role.Odd) at_step(1) public {
        int amount;
        amount = ((((! ! Even_c_done) && (! ! Odd_c_done))) ? (((Even_c == Odd_c)) ? (- int(10)) : int(10)) : (((! Even_c_done && (! ! Odd_c_done))) ? int(10) : (- int(100))));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
