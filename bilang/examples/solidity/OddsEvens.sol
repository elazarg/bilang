pragma solidity ^0.4.22;
contract OddsEvens {
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
    function join_Odd(uint salt) at_step(0) public payable {
        require(keccak256(salt) == bytes32(commitsOdd[msg.sender]));
        if (chosenRoleOdd != address(0x0))
             require(timesOdd[msg.sender] < timesOdd[chosenRoleOdd]);
        role[msg.sender] = Role.Odd;
        balanceOf[msg.sender] = msg.value;
        chosenRoleOdd = msg.sender;
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
    mapping(address => bytes32) commitsEven;
    mapping(address => uint) timesEven;
    bool halfStepEven;
    function join_commit_Even(bytes32 c) at_step(1) public {
        require(commitsEven[msg.sender] == bytes32(0));
        require(!halfStepEven);
        commitsEven[msg.sender] = c;
        timesEven[msg.sender] = block.timestamp;
    }
    event BroadcastHalfEven();
    function __nextHalfStepEven() at_step(1) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepEven == false);
        emit BroadcastHalfEven();
        halfStepEven = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleEven;
    function join_Even(uint salt) at_step(1) public payable {
        require(keccak256(salt) == bytes32(commitsEven[msg.sender]));
        if (chosenRoleEven != address(0x0))
             require(timesEven[msg.sender] < timesEven[chosenRoleEven]);
        role[msg.sender] = Role.Even;
        balanceOf[msg.sender] = msg.value;
        chosenRoleEven = msg.sender;
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
    bool Odd_c;
    bool Odd_c_done;
    bool done_Odd_2;
    function yield_Odd2(bool _c) at_step(2) public {
        require(role[msg.sender] == Role.Odd);
        require(!done_Odd_2);
        require(true);
        Odd_c = _c;
        Odd_c_done = true;
        done_Odd_2 = true;
    }
    bool Even_c;
    bool Even_c_done;
    bool done_Even_2;
    function yield_Even2(bool _c) at_step(2) public {
        require(role[msg.sender] == Role.Even);
        require(!done_Even_2);
        require(true);
        Even_c = _c;
        Even_c_done = true;
        done_Even_2 = true;
    }
    event Broadcast2(); // TODO: add params
    function __nextStep2() at_step(2) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast2();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 2
    function withdraw_3_Even() by(Role.Even) public at_step(3) {
        require(role[msg.sender] == Role.Even);
        // uint amount = balanceOf[msg.sender];
        uint amount;
        bool freshVar23;
        {
        bool freshVar24;
        {
        bool freshVar25;
        freshVar25 = Even_c_done;
        freshVar24 = ! freshVar25;
        }
        bool freshVar26;
        {
        bool freshVar27;
        freshVar27 = Odd_c_done;
        freshVar26 = ! freshVar27;
        }
        freshVar23 = freshVar24 && freshVar26;
        }
        if (freshVar23) { 
        amount = (((Even_c == Odd_c)) ? 10 : (- 10));
        } else {
        bool freshVar28;
        {
        bool freshVar29;
        freshVar29 = Even_c_done;
        bool freshVar30;
        {
        bool freshVar31;
        freshVar31 = Odd_c_done;
        freshVar30 = ! freshVar31;
        }
        freshVar28 = freshVar29 && freshVar30;
        }
        if (freshVar28) { 
        amount = (- 100);
        } else {
        amount = (- 100);
        }
        }
        // balanceOf[msg.sender] = 0;
        msg.sender.transfer(amount);
    }
    function withdraw_3_Odd() by(Role.Odd) public at_step(3) {
        require(role[msg.sender] == Role.Odd);
        // uint amount = balanceOf[msg.sender];
        uint amount;
        bool freshVar32;
        {
        bool freshVar33;
        {
        bool freshVar34;
        freshVar34 = Even_c_done;
        freshVar33 = ! freshVar34;
        }
        bool freshVar35;
        {
        bool freshVar36;
        freshVar36 = Odd_c_done;
        freshVar35 = ! freshVar36;
        }
        freshVar32 = freshVar33 && freshVar35;
        }
        if (freshVar32) { 
        amount = (((Even_c == Odd_c)) ? (- 10) : 10);
        } else {
        bool freshVar37;
        {
        bool freshVar38;
        freshVar38 = Even_c_done;
        bool freshVar39;
        {
        bool freshVar40;
        freshVar40 = Odd_c_done;
        freshVar39 = ! freshVar40;
        }
        freshVar37 = freshVar38 && freshVar39;
        }
        if (freshVar37) { 
        amount = 10;
        } else {
        amount = (- 100);
        }
        }
        // balanceOf[msg.sender] = 0;
        msg.sender.transfer(amount);
    }
}
