pragma solidity ^0.4.22;
contract Prisoners {
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
    bool A_c;
    bool A_c_done;
    bool done_A_2;
    function yield_A2(bool _c) at_step(2) public {
        require(role[msg.sender] == Role.A);
        require(!done_A_2);
        require(true);
        A_c = _c;
        A_c_done = true;
        done_A_2 = true;
    }
    bool B_c;
    bool B_c_done;
    bool done_B_2;
    function yield_B2(bool _c) at_step(2) public {
        require(role[msg.sender] == Role.B);
        require(!done_B_2);
        require(true);
        B_c = _c;
        B_c_done = true;
        done_B_2 = true;
    }
    event Broadcast2(); // TODO: add params
    function __nextStep2() at_step(2) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast2();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 2
    function withdraw_3_A() by(Role.A) public at_step(3) {
        require(role[msg.sender] == Role.A);
        // uint amount = balanceOf[msg.sender];
        uint amount;
        bool freshVar59;
        {
        bool freshVar60;
        {
        bool freshVar61;
        freshVar61 = A_c_done;
        freshVar60 = ! freshVar61;
        }
        bool freshVar62;
        {
        bool freshVar63;
        freshVar63 = B_c_done;
        freshVar62 = ! freshVar63;
        }
        freshVar59 = freshVar60 && freshVar62;
        }
        if (freshVar59) { 
        amount = (((A_c && B_c)) ? (- 2) : (((A_c && (! B_c))) ? 0 : ((((! A_c) && B_c)) ? (- 3) : (- 1))));
        } else {
        bool freshVar64;
        freshVar64 = A_c_done;
        if (freshVar64) { 
        amount = (- 100);
        } else {
        amount = 10;
        }
        }
        // balanceOf[msg.sender] = 0;
        msg.sender.transfer(amount);
    }
    function withdraw_3_B() by(Role.B) public at_step(3) {
        require(role[msg.sender] == Role.B);
        // uint amount = balanceOf[msg.sender];
        uint amount;
        bool freshVar65;
        {
        bool freshVar66;
        {
        bool freshVar67;
        freshVar67 = A_c_done;
        freshVar66 = ! freshVar67;
        }
        bool freshVar68;
        {
        bool freshVar69;
        freshVar69 = B_c_done;
        freshVar68 = ! freshVar69;
        }
        freshVar65 = freshVar66 && freshVar68;
        }
        if (freshVar65) { 
        amount = (((A_c && B_c)) ? (- 2) : (((A_c && (! B_c))) ? (- 3) : ((((! A_c) && B_c)) ? 0 : (- 1))));
        } else {
        bool freshVar70;
        freshVar70 = A_c_done;
        if (freshVar70) { 
        amount = 10;
        } else {
        amount = (- 100);
        }
        }
        // balanceOf[msg.sender] = 0;
        msg.sender.transfer(amount);
    }
}
