contract OddsEvens {
    uint Odd_amount;
    uint Even_amount;

    // roles
    enum Role { Odd, Even }
    mapping(address => Role) role;

    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }

    // Step
    uint constant STEP_TIME = 500;
    bool step;
    uint __lastStep;
    event Completed(uint i);

    modifier at_step(int _step) {
        require(step == _step);
        _;
    }

    // join  Odd()         join Even();

    function joinOdd() at_step(0) {
        require(role[msg.sender] == address(0x0));
        role[msg.sender] = Role.Odd;
    }

    function joinEven() at_step(0) {
        require(role[msg.sender] == address(0x0));
        role[msg.sender] = Role.Even;
    }

    event Broadcast0();
    function __nextStep0() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Completed(step);
        Broadcast0();
        __lastStep = block.timestamp;
    }

    // yield Odd(c: bool) yield Even(c: bool);
    // hide
    uint256 hidden_Odd_c;
    uint256 hidden_Even_c;

    function hide_Odd_c(uint256 commitment) at_step(1) by(Role.Odd) {
        hidden_Odd_c = commitment;
    }

    function hide_Even_c(uint256 commitment) at_step(1) by(Role.Even) {
        hidden_Even_c = commitment;
    }

    event Broadcast1();
    function __nextStep1() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast1();
        __lastStep = block.timestamp;
    }

    // yield Odd(c: bool) yield Even(c: bool);
    // reveal

    bool Odd_c;
    bool Odd_c_initialized;

    bool Even_c;
    bool Even_c_initialized;

    function reveal_Odd_c(bool value, uint salt) at_step(2) by(Role.Odd) {
        require(sha3(value, salt) == bytes32(hidden_Odd_c));
        Odd_c = value;
        Odd_c_initialized = true;
    }

    function reveal_Even_c(uint value) at_step(2) by(Role.Even) {
        require(sha3(value, salt) == bytes32(hidden_Even_c));
        Even_c = value;
        Even_c_initialized = true;
    }

    event Broadcast2(bool Odd_c, bool Even_c);
    function __nextStep2() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast2(Odd_c, Even_c);
        __lastStep = block.timestamp;
    }

    function withdraw_Odd() by(Role.Odd) returns (uint[3]) {
        if (Even.c != null && Odd.c != null) {
            int p = (Even.c == Odd.c) ? 10 : -10;
            Odd_amount = -p;
        } else if (Even.c == null && Odd.c != null) {
            Odd_amount = -100;
        } else {
            Odd_amount = -100;
        }
    }

    function withdraw_Even() by(Role.Even) returns (uint[3]) {
        if (Even.c != null && Odd.c != null) {
            int p = (Even.c == Odd.c) ? 10 : -10;
            Even_amount = p;
        } else if (Even.c == null && Odd.c != null) {
            Even_amount =10;
        } else {
            Even_amount = -100;
        }
    }
}
