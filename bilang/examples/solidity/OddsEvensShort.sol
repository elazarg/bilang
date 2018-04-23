pragma solidity ^0.4.22;
contract OddsEvensShort {
    // roles
    enum Role { None, Odd, Even }
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
    mapping(address => bytes32) commitsOdd;
    mapping(address => uint) timesOdd;
    bool halfStepOdd;
    function join_commit_Odd(bytes32 c) at_step(0) public {
        require(commitsOdd[msg.sender] == bytes32(0));
        require(!halfStepOdd);
        commitsOdd[msg.sender] = c;
        timesOdd[msg.sender] = block.timestamp;
    }
    event BroadcastHalfOdd();
    function __nextHalfStepOdd() at_step(0) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepOdd == false);
        emit BroadcastHalfOdd();
        halfStepOdd = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleOdd;
    bool Odd_c;
    bool Odd_c_done;
    function join_Odd(bool _c, uint salt) at_step(0) public payable {
        require(keccak256(_c, salt) == bytes32(commitsOdd[msg.sender]));
        if (chosenRoleOdd != address(0x0))
             require(timesOdd[msg.sender] < timesOdd[chosenRoleOdd]);
        role[msg.sender] = Role.Odd;
        balanceOf[msg.sender] = msg.value;
        chosenRoleOdd = msg.sender;
        require(true);
        Odd_c = _c;
        Odd_c_done = true;
    }
    mapping(address => bytes32) commitsEven;
    mapping(address => uint) timesEven;
    bool halfStepEven;
    function join_commit_Even(bytes32 c) at_step(0) public {
        require(commitsEven[msg.sender] == bytes32(0));
        require(!halfStepEven);
        commitsEven[msg.sender] = c;
        timesEven[msg.sender] = block.timestamp;
    }
    event BroadcastHalfEven();
    function __nextHalfStepEven() at_step(0) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepEven == false);
        emit BroadcastHalfEven();
        halfStepEven = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleEven;
    bool Even_c;
    bool Even_c_done;
    function join_Even(bool _c, uint salt) at_step(0) public payable {
        require(keccak256(_c, salt) == bytes32(commitsEven[msg.sender]));
        if (chosenRoleEven != address(0x0))
             require(timesEven[msg.sender] < timesEven[chosenRoleEven]);
        role[msg.sender] = Role.Even;
        balanceOf[msg.sender] = msg.value;
        chosenRoleEven = msg.sender;
        require(true);
        Even_c = _c;
        Even_c_done = true;
    }
    event Broadcast0(); // TODO: add params
    function __nextStep0() at_step(0) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast0();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 0
    function withdraw_1_Even() by(Role.Even) public at_step(1) {
        require(role[msg.sender] == Role.Even);
        int amount;
        bool freshVar41;
        {
        bool freshVar42;
        {
        bool freshVar43;
        freshVar43 = Even_c_done;
        freshVar42 = ! freshVar43;
        }
        bool freshVar44;
        {
        bool freshVar45;
        freshVar45 = Odd_c_done;
        freshVar44 = ! freshVar45;
        }
        freshVar41 = freshVar42 && freshVar44;
        }
        if (freshVar41) { 
        amount = (((Even_c == Odd_c)) ? int(10) : (- int(10)));
        } else {
        bool freshVar46;
        {
        bool freshVar47;
        freshVar47 = Even_c_done;
        bool freshVar48;
        {
        bool freshVar49;
        freshVar49 = Odd_c_done;
        freshVar48 = ! freshVar49;
        }
        freshVar46 = freshVar47 && freshVar48;
        }
        if (freshVar46) { 
        amount = (- int(100));
        } else {
        amount = (- int(100));
        }
        }
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_1_Odd() by(Role.Odd) public at_step(1) {
        require(role[msg.sender] == Role.Odd);
        int amount;
        bool freshVar50;
        {
        bool freshVar51;
        {
        bool freshVar52;
        freshVar52 = Even_c_done;
        freshVar51 = ! freshVar52;
        }
        bool freshVar53;
        {
        bool freshVar54;
        freshVar54 = Odd_c_done;
        freshVar53 = ! freshVar54;
        }
        freshVar50 = freshVar51 && freshVar53;
        }
        if (freshVar50) { 
        amount = (((Even_c == Odd_c)) ? (- int(10)) : int(10));
        } else {
        bool freshVar55;
        {
        bool freshVar56;
        freshVar56 = Even_c_done;
        bool freshVar57;
        {
        bool freshVar58;
        freshVar58 = Odd_c_done;
        freshVar57 = ! freshVar58;
        }
        freshVar55 = freshVar56 && freshVar57;
        }
        if (freshVar55) { 
        amount = int(10);
        } else {
        amount = (- int(100));
        }
        }
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
