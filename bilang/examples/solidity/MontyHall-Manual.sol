contract MontyHall {
    uint Host_amount;
    uint Guest_amount;

    // roles
    enum Role { Host, Guest }
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

    // join  Host();

    function joinHost() at_step(0) {
        require(role[msg.sender] == address(0x0));
        role[msg.sender] = Role.Host;
    }

    event Broadcast0();
    function __nextStep0() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast0();
        __lastStep = block.timestamp;
    }

    // join Guest();
    function joinGuest() at_step(1) {
        require(role[msg.sender] == address(0x0));
        role[msg.sender] = Role.Guest;
    }

    event Broadcast1();
    function __nextStep0() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast1();
        __lastStep = block.timestamp;
    }

    // yield Host(c: bool) yield Guest(c: bool);
    // hide
    uint256 hidden_Host_c;
    uint256 hidden_Guest_c;

    function hide_Host_c(uint256 commitment) at_step(1) by(Role.Host) {
        hidden_Host_c = commitment;
    }

    function hide_Guest_c(uint256 commitment) at_step(1) by(Role.Guest) {
        hidden_Guest_c = commitment;
    }

    event Broadcast1();
    function __nextStep1() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast1();
        __lastStep = block.timestamp;
    }

    // yield Host(c: bool) yield Guest(c: bool);
    // reveal

    bool Host_c;
    bool Host_c_initialized;

    bool Guest_c;
    bool Guest_c_initialized;

    function reveal_Host_c(bool value, uint salt) at_step(2) by(Role.Host) {
        require(sha3(value, salt) == bytes32(hidden_Host_c));
        Host_c = value;
        Host_c_initialized = true;
    }

    function reveal_Guest_c(uint value) at_step(2) by(Role.Guest) {
        require(sha3(value, salt) == bytes32(hidden_Guest_c));
        Guest_c = value;
        Guest_c_initialized = true;
    }

    event Broadcast2(bool Host_c, bool Guest_c);
    function __nextStep2() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast2(Host_c, Guest_c);
        __lastStep = block.timestamp;
    }

    function withdraw_Host() by(Role.Host) returns (uint[3]) {
        if (Guest.c != null && Host.c != null) {
            int p = (Guest.c == Host.c) ? 10 : -10;
            Host_amount = -p;
        } else if (Guest.c == null && Host.c != null) {
            Host_amount = -100;
        } else {
            Host_amount = -100;
        }
    }

    function withdraw_Guest() by(Role.Guest) returns (uint[3]) {
        if (Guest.c != null && Host.c != null) {
            int p = (Guest.c == Host.c) ? 10 : -10;
            Guest_amount = p;
        } else if (Guest.c == null && Host.c != null) {
            Guest_amount =10;
        } else {
            Guest_amount = -100;
        }
    }
}
