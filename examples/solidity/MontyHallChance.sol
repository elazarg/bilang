
pragma solidity ^0.8.31;
contract MontyHallChance {
    constructor() {
        lastTs = block.timestamp;
    }
    function keccak(bool x, uint256 salt) public pure returns (bytes32) {
        return keccak256(abi.encodePacked(x, salt));
    }
    // Step
    uint256 public constant STEP_TIME = 500;
    uint256 public step;
    uint256 public lastTs;
    modifier at_step(uint256 _step) {
        require(step == _step, "wrong step");
        // require(block.timestamp < lastTs + STEP_TIME, "step expired");
        _;
    }
    // roles
    enum Role { None, Host, Guest }
    mapping(address => Role) public role;
    mapping(address => uint256) public balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r, "bad role");
        _;
    }
    // step 0
    bool public doneHost;
    function join_Host() public payable by(Role.None) at_step(0) {
        require(!doneHost, "already joined");
        role[msg.sender] = Role.Host;
        require(msg.value == 100, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        doneHost = true;
    }
    event Broadcast0(); // TODO: add params
    function __nextStep0() public {
        require(step == 0, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast0();
        step = 1;
        lastTs = block.timestamp;
    }
    // end 0
    // step 1
    bool public doneGuest;
    function join_Guest() public payable by(Role.None) at_step(1) {
        require(!doneGuest, "already joined");
        role[msg.sender] = Role.Guest;
        require(msg.value == 100, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        doneGuest = true;
    }
    event Broadcast1(); // TODO: add params
    function __nextStep1() public {
        require(step == 1, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast1();
        step = 2;
        lastTs = block.timestamp;
    }
    // end 1
    // step 2
    uint256 public Host_hidden_car;
    bool public Host_hidden_car_done;
    bool public done_Host_2;
    function yield_Host2(uint256 _hidden_car) public by(Role.Host) at_step(2) {
        require(!done_Host_2, "done");
        require(true, "where");
        Host_hidden_car = _hidden_car;
        Host_hidden_car_done = true;
        done_Host_2 = true;
    }
    event Broadcast2(); // TODO: add params
    function __nextStep2() public {
        require(step == 2, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast2();
        step = 3;
        lastTs = block.timestamp;
    }
    // end 2
    // step 3
    int256 public Guest_d;
    bool public Guest_d_done;
    bool public done_Guest_3;
    function yield_Guest3(int256 _d) public by(Role.Guest) at_step(3) {
        require(!done_Guest_3, "done");
        require(true, "where");
        Guest_d = _d;
        Guest_d_done = true;
        done_Guest_3 = true;
    }
    event Broadcast3(); // TODO: add params
    function __nextStep3() public {
        require(step == 3, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast3();
        step = 4;
        lastTs = block.timestamp;
    }
    // end 3
    // step 4
    int256 public Host_goat;
    bool public Host_goat_done;
    bool public done_Host_4;
    function yield_Host4(int256 _goat) public by(Role.Host) at_step(4) {
        require(!done_Host_4, "done");
        require((Host_goat != Guest_d), "where");
        Host_goat = _goat;
        Host_goat_done = true;
        done_Host_4 = true;
    }
    event Broadcast4(); // TODO: add params
    function __nextStep4() public {
        require(step == 4, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast4();
        step = 5;
        lastTs = block.timestamp;
    }
    // end 4
    // step 5
    bool public Guest_switch;
    bool public Guest_switch_done;
    bool public done_Guest_5;
    function yield_Guest5(bool _switch) public by(Role.Guest) at_step(5) {
        require(!done_Guest_5, "done");
        require(true, "where");
        Guest_switch = _switch;
        Guest_switch_done = true;
        done_Guest_5 = true;
    }
    event Broadcast5(); // TODO: add params
    function __nextStep5() public {
        require(step == 5, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast5();
        step = 6;
        lastTs = block.timestamp;
    }
    // end 5
    // step 6
    int256 public Host_car;
    bool public Host_car_done;
    bool public done_Host_6;
    function reveal_Host6(int256 _car, uint256 salt) public by(Role.Host) at_step(6) {
        require(!done_Host_6, "done");
        require(keccak256(abi.encodePacked(_car, salt)) == bytes32(Host_hidden_car), "bad reveal");
        require((Host_goat != Host_car), "where");
        Host_car = _car;
        Host_car_done = true;
        done_Host_6 = true;
    }
    event Broadcast6(); // TODO: add params
    function __nextStep6() public {
        require(step == 6, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast6();
        step = 7;
        lastTs = block.timestamp;
    }
    // end 6
    function withdraw_7_Guest() public by(Role.Guest) at_step(7) {
        int256 delta = ((((Host_car_done && Host_goat_done) && Guest_switch_done)) ? ((((Guest_d != Host_car) == Guest_switch)) ? int256(20) : (- int256(20))) : (((! Host_car_done || ! Host_goat_done)) ? int256(20) : (- int256(100))));
        uint256 bal = balanceOf[msg.sender];
        uint256 amount;
        if (delta >= 0) {
            amount = bal + uint256(delta);
        } else {
            uint256 d = uint256(-delta);
            require(bal >= d, "insufficient");
            amount = bal - d;
        }
        // Effects first
        balanceOf[msg.sender] = 0;
        // Interaction
        (bool ok, ) = payable(msg.sender).call{value: amount}("");
        require(ok, "ETH send failed");
    }
    function withdraw_7_Host() public by(Role.Host) at_step(7) {
        int256 delta = ((((Host_car_done && Host_goat_done) && Guest_switch_done)) ? int256(0) : (((! Host_car_done || ! Host_goat_done)) ? (- int256(100)) : int256(0)));
        uint256 bal = balanceOf[msg.sender];
        uint256 amount;
        if (delta >= 0) {
            amount = bal + uint256(delta);
        } else {
            uint256 d = uint256(-delta);
            require(bal >= d, "insufficient");
            amount = bal - d;
        }
        // Effects first
        balanceOf[msg.sender] = 0;
        // Interaction
        (bool ok, ) = payable(msg.sender).call{value: amount}("");
        require(ok, "ETH send failed");
    }
    // Reject stray ETH by default
    receive() external payable {
        revert("direct ETH not allowed");
    }
}
