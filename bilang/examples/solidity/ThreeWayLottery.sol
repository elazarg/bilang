
contract ThreeWayLottery {
    // roles
    enum Role { Issuer, Alice, Bob }
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
    function join_Issuer() at_step(0) {
        require(role[msg.sender] == address(0x0));
        role[msg.sender] = Role.Issuer;
        require(true);
    }
    event Broadcast0();
    function __nextStep0() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast0();
        __lastStep = block.timestamp;
    }
    function join_Alice() at_step(1) {
        require(role[msg.sender] == address(0x0));
        role[msg.sender] = Role.Alice;
        require(true);
    }
    event Broadcast1();
    function __nextStep1() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast1();
        __lastStep = block.timestamp;
    }
    function join_Bob() at_step(2) {
        require(role[msg.sender] == address(0x0));
        role[msg.sender] = Role.Bob;
        require(true);
    }
    event Broadcast2();
    function __nextStep2() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast2();
        __lastStep = block.timestamp;
    }
    uint c;
    function yield_Issuer3(uint _c) at_step(3) {
        require(role[msg.sender] == Role.Issuer);
        require(true);
        Issuer_c = _c;
        Issuer_c_done = true;
    }
    uint c;
    function yield_Alice3(uint _c) at_step(3) {
        require(role[msg.sender] == Role.Alice);
        require(true);
        Alice_c = _c;
        Alice_c_done = true;
    }
    uint c;
    function yield_Bob3(uint _c) at_step(3) {
        require(role[msg.sender] == Role.Bob);
        require(true);
        Bob_c = _c;
        Bob_c_done = true;
    }
    event Broadcast3();
    function __nextStep3() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast3();
        __lastStep = block.timestamp;
    }
    int Issuer_c;
    function reveal_Issuer4(int _c, uint salt) at_step(4) {
        require(role[msg.sender] == Role.Issuer);
        require(sha3(_c, salt) == bytes32(hidden_c));
        require(true);
        Issuer_c = _c;
        c_done = true;
    }
    int Alice_c;
    function reveal_Alice4(int _c, uint salt) at_step(4) {
        require(role[msg.sender] == Role.Alice);
        require(sha3(_c, salt) == bytes32(hidden_c));
        require(true);
        Alice_c = _c;
        c_done = true;
    }
    int Bob_c;
    function reveal_Bob4(int _c, uint salt) at_step(4) {
        require(role[msg.sender] == Role.Bob);
        require(sha3(_c, salt) == bytes32(hidden_c));
        require(true);
        Bob_c = _c;
        c_done = true;
    }
    event Broadcast4();
    function __nextStep4() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast4();
        __lastStep = block.timestamp;
    }
}
