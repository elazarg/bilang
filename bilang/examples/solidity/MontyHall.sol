pragma solidity ^0.4.22;
contract MontyHall {
    // roles
    enum Role { None, Host, Guest }
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
    mapping(address => bytes32) commitsHost;
    mapping(address => uint) timesHost;
    bool halfStepHost;
    function join_commit_Host(bytes32 c) at_step(0) public {
        require(commitsHost[msg.sender] == bytes32(0));
        require(!halfStepHost);
        commitsHost[msg.sender] = c;
        timesHost[msg.sender] = block.timestamp;
    }
    event BroadcastHalfHost();
    function __nextHalfStepHost() at_step(0) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepHost == false);
        emit BroadcastHalfHost();
        halfStepHost = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleHost;
    function join_Host(uint salt) at_step(0) public payable {
        require(keccak256(salt) == bytes32(commitsHost[msg.sender]));
        if (chosenRoleHost != address(0x0))
             require(timesHost[msg.sender] < timesHost[chosenRoleHost]);
        role[msg.sender] = Role.Host;
        balanceOf[msg.sender] = msg.value;
        chosenRoleHost = msg.sender;
        require(true);
    }
    mapping(address => bytes32) commitsGuest;
    mapping(address => uint) timesGuest;
    bool halfStepGuest;
    function join_commit_Guest(bytes32 c) at_step(0) public {
        require(commitsGuest[msg.sender] == bytes32(0));
        require(!halfStepGuest);
        commitsGuest[msg.sender] = c;
        timesGuest[msg.sender] = block.timestamp;
    }
    event BroadcastHalfGuest();
    function __nextHalfStepGuest() at_step(0) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepGuest == false);
        emit BroadcastHalfGuest();
        halfStepGuest = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleGuest;
    function join_Guest(uint salt) at_step(0) public payable {
        require(keccak256(salt) == bytes32(commitsGuest[msg.sender]));
        if (chosenRoleGuest != address(0x0))
             require(timesGuest[msg.sender] < timesGuest[chosenRoleGuest]);
        role[msg.sender] = Role.Guest;
        balanceOf[msg.sender] = msg.value;
        chosenRoleGuest = msg.sender;
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
    uint Host_hidden_car;
    bool Host_hidden_car_done;
    bool done_Host_1;
    function yield_Host1(uint _hidden_car) at_step(1) public {
        require(role[msg.sender] == Role.Host);
        require(!done_Host_1);
        require(true);
        Host_hidden_car = _hidden_car;
        Host_hidden_car_done = true;
        done_Host_1 = true;
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
    int Guest_d;
    bool Guest_d_done;
    bool done_Guest_2;
    function yield_Guest2(int _d) at_step(2) public {
        require(role[msg.sender] == Role.Guest);
        require(!done_Guest_2);
        require(true);
        Guest_d = _d;
        Guest_d_done = true;
        done_Guest_2 = true;
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
    int Host_goat;
    bool Host_goat_done;
    bool done_Host_3;
    function yield_Host3(int _goat) at_step(3) public {
        require(role[msg.sender] == Role.Host);
        require(!done_Host_3);
        require((Host_goat != Guest_d));
        Host_goat = _goat;
        Host_goat_done = true;
        done_Host_3 = true;
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
    bool Guest_switch;
    bool Guest_switch_done;
    bool done_Guest_4;
    function yield_Guest4(bool _switch) at_step(4) public {
        require(role[msg.sender] == Role.Guest);
        require(!done_Guest_4);
        require(true);
        Guest_switch = _switch;
        Guest_switch_done = true;
        done_Guest_4 = true;
    }
    event Broadcast4(); // TODO: add params
    function __nextStep4() at_step(4) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast4();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 4
    // step 5
    int Host_car;
    bool Host_car_done;
    bool done_Host_5;
    function reveal_Host5(int _car, uint salt) at_step(5) public {
        require(role[msg.sender] == Role.Host);
        require(!done_Host_5);
        require(keccak256(_car, salt) == bytes32(Host_hidden_car));
        require((Host_goat != Host_car));
        Host_car = _car;
        Host_car_done = true;
        done_Host_5 = true;
    }
    event Broadcast5(); // TODO: add params
    function __nextStep5() at_step(5) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast5();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 5
}
