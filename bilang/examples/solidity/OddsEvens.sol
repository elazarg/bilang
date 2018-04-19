
contract OddsEvens {
    // roles
    enum Role { Odd, Even }
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
    function join_Odd() at_step(0) {
        require(role[msg.sender] == address(0x0));
        role[msg.sender] = Role.Odd;
        require(true);
    }
    function join_Even() at_step(0) {
        require(role[msg.sender] == address(0x0));
        role[msg.sender] = Role.Even;
        require(true);
    }
    event Broadcast0();
    function __nextStep0() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast0();
        __lastStep = block.timestamp;
    }
    uint c;
    function yield_Odd1(uint _c) at_step(1) {
        require(role[msg.sender] == Role.Odd);
        require(true);
        Odd_c = _c;
        Odd_c_done = true;
    }
    uint c;
    function yield_Even1(uint _c) at_step(1) {
        require(role[msg.sender] == Role.Even);
        require(true);
        Even_c = _c;
        Even_c_done = true;
    }
    event Broadcast1();
    function __nextStep1() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast1();
        __lastStep = block.timestamp;
    }
    bool Odd_c;
    function reveal_Odd2(bool _c, uint salt) at_step(2) {
        require(role[msg.sender] == Role.Odd);
        require(sha3(_c, salt) == bytes32(hidden_c));
        require(true);
        Odd_c = _c;
        c_done = true;
    }
    bool Even_c;
    function reveal_Even2(bool _c, uint salt) at_step(2) {
        require(role[msg.sender] == Role.Even);
        require(sha3(_c, salt) == bytes32(hidden_c));
        require(true);
        Even_c = _c;
        c_done = true;
    }
    event Broadcast2();
    function __nextStep2() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast2();
        __lastStep = block.timestamp;
    }
}
