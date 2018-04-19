
contract MontyHall {
    // roles
    enum Role { Host, Guest }
    mapping(address => Role) role;
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
        _;
    }
    function join_Host() at_step(0) {
        require(role[msg.sender] == address(0x0));
        role[msg.sender] = Role.Host;
        require(true);
    }
    function join_Guest() at_step(0) {
        require(role[msg.sender] == address(0x0));
        role[msg.sender] = Role.Guest;
        require(true);
    }
    event Broadcast0();
    function __nextStep0() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast0();
        __lastStep = block.timestamp;
    }
    uint car;
    function yield_Host1(uint _car) at_step(1) {
        require(role[msg.sender] == Role.Host);
        require(true);
        Host_car = _car;
        Host_car_done = true;
    }
    event Broadcast1();
    function __nextStep1() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast1();
        __lastStep = block.timestamp;
    }
    int d;
    function yield_Guest2(int _d) at_step(2) {
        require(role[msg.sender] == Role.Guest);
        require(true);
        Guest_d = _d;
        Guest_d_done = true;
    }
    event Broadcast2();
    function __nextStep2() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast2();
        __lastStep = block.timestamp;
    }
    int goat;
    function yield_Host3(int _goat) at_step(3) {
        require(role[msg.sender] == Role.Host);
        require((Host_goat != Guest_d));
        Host_goat = _goat;
        Host_goat_done = true;
    }
    event Broadcast3();
    function __nextStep3() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast3();
        __lastStep = block.timestamp;
    }
    bool switch;
    function yield_Guest4(bool _switch) at_step(4) {
        require(role[msg.sender] == Role.Guest);
        require(true);
        Guest_switch = _switch;
        Guest_switch_done = true;
    }
    event Broadcast4();
    function __nextStep4() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast4();
        __lastStep = block.timestamp;
    }
    int Host_car;
    function reveal_Host5(int _car, uint salt) at_step(5) {
        require(role[msg.sender] == Role.Host);
        require(sha3(_car, salt) == bytes32(hidden_car));
        require((Host_goat != Host_car));
        Host_car = _car;
        car_done = true;
    }
    event Broadcast5();
    function __nextStep5() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast5();
        __lastStep = block.timestamp;
    }
}
