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
        require(msg.value == 100);
        balanceOf[msg.sender] = msg.value;
        chosenRoleHost = msg.sender;
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
    mapping(address => bytes32) commitsGuest;
    mapping(address => uint) timesGuest;
    bool halfStepGuest;
    function join_commit_Guest(bytes32 c) at_step(1) public {
        require(commitsGuest[msg.sender] == bytes32(0));
        require(!halfStepGuest);
        commitsGuest[msg.sender] = c;
        timesGuest[msg.sender] = block.timestamp;
    }
    event BroadcastHalfGuest();
    function __nextHalfStepGuest() at_step(1) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepGuest == false);
        emit BroadcastHalfGuest();
        halfStepGuest = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleGuest;
    function join_Guest(uint salt) at_step(1) public payable {
        require(keccak256(salt) == bytes32(commitsGuest[msg.sender]));
        if (chosenRoleGuest != address(0x0))
             require(timesGuest[msg.sender] < timesGuest[chosenRoleGuest]);
        role[msg.sender] = Role.Guest;
        require(msg.value == 100);
        balanceOf[msg.sender] = msg.value;
        chosenRoleGuest = msg.sender;
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
    uint Host_hidden_car;
    bool Host_hidden_car_done;
    bool done_Host_2;
    function yield_Host2(uint _hidden_car) at_step(2) public {
        require(role[msg.sender] == Role.Host);
        require(!done_Host_2);
        require(true);
        Host_hidden_car = _hidden_car;
        Host_hidden_car_done = true;
        done_Host_2 = true;
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
    int Guest_d;
    bool Guest_d_done;
    bool done_Guest_3;
    function yield_Guest3(int _d) at_step(3) public {
        require(role[msg.sender] == Role.Guest);
        require(!done_Guest_3);
        require(true);
        Guest_d = _d;
        Guest_d_done = true;
        done_Guest_3 = true;
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
    int Host_goat;
    bool Host_goat_done;
    bool done_Host_4;
    function yield_Host4(int _goat) at_step(4) public {
        require(role[msg.sender] == Role.Host);
        require(!done_Host_4);
        require((Host_goat != Guest_d));
        Host_goat = _goat;
        Host_goat_done = true;
        done_Host_4 = true;
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
    bool Guest_switch;
    bool Guest_switch_done;
    bool done_Guest_5;
    function yield_Guest5(bool _switch) at_step(5) public {
        require(role[msg.sender] == Role.Guest);
        require(!done_Guest_5);
        require(true);
        Guest_switch = _switch;
        Guest_switch_done = true;
        done_Guest_5 = true;
    }
    event Broadcast5(); // TODO: add params
    function __nextStep5() at_step(5) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast5();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 5
    // step 6
    int Host_car;
    bool Host_car_done;
    bool done_Host_6;
    function reveal_Host6(int _car, uint salt) at_step(6) public {
        require(role[msg.sender] == Role.Host);
        require(!done_Host_6);
        require(keccak256(_car, salt) == bytes32(Host_hidden_car));
        require((Host_goat != Host_car));
        Host_car = _car;
        Host_car_done = true;
        done_Host_6 = true;
    }
    event Broadcast6(); // TODO: add params
    function __nextStep6() at_step(6) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast6();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 6
    function withdraw_7_Guest() by(Role.Guest) public at_step(7) {
        require(role[msg.sender] == Role.Guest);
        int amount;
        bool freshVar1;
        {
        bool freshVar2;
        {
        bool freshVar3;
        {
        bool freshVar4;
        freshVar4 = Host_car_done;
        freshVar3 = ! freshVar4;
        }
        bool freshVar5;
        {
        bool freshVar6;
        freshVar6 = Host_goat_done;
        freshVar5 = ! freshVar6;
        }
        freshVar2 = freshVar3 && freshVar5;
        }
        bool freshVar7;
        {
        bool freshVar8;
        freshVar8 = Guest_switch_done;
        freshVar7 = ! freshVar8;
        }
        freshVar1 = freshVar2 && freshVar7;
        }
        if (freshVar1) { 
        amount = ((((Guest_d != Host_car) == Guest_switch)) ? int(20) : (- int(20)));
        } else {
        bool freshVar9;
        {
        bool freshVar10;
        freshVar10 = Host_car_done;
        bool freshVar11;
        freshVar11 = Host_goat_done;
        freshVar9 = freshVar10 || freshVar11;
        }
        if (freshVar9) { 
        amount = int(20);
        } else {
        amount = (- int(100));
        }
        }
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_7_Host() by(Role.Host) public at_step(7) {
        require(role[msg.sender] == Role.Host);
        int amount;
        bool freshVar12;
        {
        bool freshVar13;
        {
        bool freshVar14;
        {
        bool freshVar15;
        freshVar15 = Host_car_done;
        freshVar14 = ! freshVar15;
        }
        bool freshVar16;
        {
        bool freshVar17;
        freshVar17 = Host_goat_done;
        freshVar16 = ! freshVar17;
        }
        freshVar13 = freshVar14 && freshVar16;
        }
        bool freshVar18;
        {
        bool freshVar19;
        freshVar19 = Guest_switch_done;
        freshVar18 = ! freshVar19;
        }
        freshVar12 = freshVar13 && freshVar18;
        }
        if (freshVar12) { 
        amount = int(0);
        } else {
        bool freshVar20;
        {
        bool freshVar21;
        freshVar21 = Host_car_done;
        bool freshVar22;
        freshVar22 = Host_goat_done;
        freshVar20 = freshVar21 || freshVar22;
        }
        if (freshVar20) { 
        amount = (- int(100));
        } else {
        amount = int(0);
        }
        }
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
