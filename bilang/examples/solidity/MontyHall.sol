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
    function join_Host() at_step(0) public payable {
        require(role[msg.sender] == Role.None);
        role[msg.sender] = Role.Host;
        balanceOf[msg.sender] = msg.value;
        require(true);
    }
    function join_Guest() at_step(0) public payable {
        require(role[msg.sender] == Role.None);
        role[msg.sender] = Role.Guest;
        balanceOf[msg.sender] = msg.value;
        require(true);
    }
    event Broadcast0(); // TODO: add params
    function __nextStep0() at_step(0) public {
        emit Broadcast0();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 0
    // step 1
    uint Host_hidden_car;
    bool Host_hidden_car_done;
    function yield_Host1(uint _hidden_car) at_step(1) public {
        require(role[msg.sender] == Role.Host);
        require(true);
        Host_hidden_car = _hidden_car;
        Host_hidden_car_done = true;
    }
    event Broadcast1(); // TODO: add params
    function __nextStep1() at_step(1) public {
        emit Broadcast1();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 1
    // step 2
    int Guest_d;
    bool Guest_d_done;
    function yield_Guest2(int _d) at_step(2) public {
        require(role[msg.sender] == Role.Guest);
        require(true);
        Guest_d = _d;
        Guest_d_done = true;
    }
    event Broadcast2(); // TODO: add params
    function __nextStep2() at_step(2) public {
        emit Broadcast2();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 2
    // step 3
    int Host_goat;
    bool Host_goat_done;
    function yield_Host3(int _goat) at_step(3) public {
        require(role[msg.sender] == Role.Host);
        require((Host_goat != Guest_d));
        Host_goat = _goat;
        Host_goat_done = true;
    }
    event Broadcast3(); // TODO: add params
    function __nextStep3() at_step(3) public {
        emit Broadcast3();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 3
    // step 4
    bool Guest_switch;
    bool Guest_switch_done;
    function yield_Guest4(bool _switch) at_step(4) public {
        require(role[msg.sender] == Role.Guest);
        require(true);
        Guest_switch = _switch;
        Guest_switch_done = true;
    }
    event Broadcast4(); // TODO: add params
    function __nextStep4() at_step(4) public {
        emit Broadcast4();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 4
    // step 5
    int Host_car;
    bool Host_car_done;
    function reveal_Host5(int _car, uint salt) at_step(5) public {
        require(role[msg.sender] == Role.Host);
        require(keccak256(_car, salt) == bytes32(Host_hidden_car));
        require((Host_goat != Host_car));
        Host_car = _car;
        Host_car_done = true;
    }
    event Broadcast5(); // TODO: add params
    function __nextStep5() at_step(5) public {
        emit Broadcast5();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 5
}
