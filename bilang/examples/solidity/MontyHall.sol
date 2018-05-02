pragma solidity ^0.4.22;
contract MontyHall {
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
    enum Role { None, Host, Guest }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
    // step 0
    bool doneHost;
    function join_Host() at_step(0) public by(Role.None) payable {
        require(!doneHost);
        role[msg.sender] = Role.Host;
        require(msg.value == 100); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneHost = true;
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
    bool doneGuest;
    function join_Guest() at_step(1) public by(Role.None) payable {
        require(!doneGuest);
        role[msg.sender] = Role.Guest;
        require(msg.value == 100); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneGuest = true;
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
    uint Host_hidden_car;
    bool Host_hidden_car_done;
    bool done_Host_2;
    function yield_Host2(uint _hidden_car) by (Role.Host) at_step(2) public {
        require(!done_Host_2);
        require(true);
        Host_hidden_car = _hidden_car;
        Host_hidden_car_done = true;
        done_Host_2 = true;
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
    int Guest_d;
    bool Guest_d_done;
    bool done_Guest_3;
    function yield_Guest3(int _d) by (Role.Guest) at_step(3) public {
        require(!done_Guest_3);
        require(true);
        Guest_d = _d;
        Guest_d_done = true;
        done_Guest_3 = true;
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
    int Host_goat;
    bool Host_goat_done;
    bool done_Host_4;
    function yield_Host4(int _goat) by (Role.Host) at_step(4) public {
        require(!done_Host_4);
        require((Host_goat != Guest_d));
        Host_goat = _goat;
        Host_goat_done = true;
        done_Host_4 = true;
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
    // step 5
    bool Guest_switch;
    bool Guest_switch_done;
    bool done_Guest_5;
    function yield_Guest5(bool _switch) by (Role.Guest) at_step(5) public {
        require(!done_Guest_5);
        require(true);
        Guest_switch = _switch;
        Guest_switch_done = true;
        done_Guest_5 = true;
    }
    event Broadcast5(); // TODO: add params
    function __nextStep5() public {
        require(step == 5);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast5();
        step = 6;
        lastBlock = block.timestamp;
    }
    // end 5
    // step 6
    int Host_car;
    bool Host_car_done;
    bool done_Host_6;
    function reveal_Host6(int _car, uint salt) by(Role.Host) at_step(6) public {
        require(!done_Host_6);
        require(keccak256(_car, salt) == bytes32(Host_hidden_car));
        require((Host_goat != Host_car));
        Host_car = _car;
        Host_car_done = true;
        done_Host_6 = true;
    }
    event Broadcast6(); // TODO: add params
    function __nextStep6() public {
        require(step == 6);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast6();
        step = 7;
        lastBlock = block.timestamp;
    }
    // end 6
    function withdraw_7_Guest() by(Role.Guest) at_step(7) public {
        int amount = (((Host_car_done && Guest_switch_done)) ? ((((Guest_d != Host_car) == Guest_switch)) ? int(20) : (- int(20))) : ((! Host_car_done) ? int(20) : (- int(100))));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_7_Host() by(Role.Host) at_step(7) public {
        int amount = (((Host_car_done && Guest_switch_done)) ? int(0) : ((! Host_car_done) ? (- int(100)) : int(0)));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
