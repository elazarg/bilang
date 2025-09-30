
pragma solidity ^0.8.31;
contract Simple {
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
    enum Role { None, A, B }
    mapping(address => Role) public role;
    mapping(address => uint256) public balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r, "bad role");
        _;
    }
    // step 0
    bool public doneA;
    function join_A() public payable by(Role.None) at_step(0) {
        require(!doneA, "already joined");
        role[msg.sender] = Role.A;
        require(msg.value == 1, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        doneA = true;
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
    bool public doneB;
    function join_B() public payable by(Role.None) at_step(1) {
        require(!doneB, "already joined");
        role[msg.sender] = Role.B;
        require(msg.value == 1, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        doneB = true;
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
    uint256 public A_hidden_c;
    bool public A_hidden_c_done;
    bool public done_A_2;
    function yield_A2(uint256 _hidden_c) public by(Role.A) at_step(2) {
        require(!done_A_2, "done");
        require(true, "where");
        A_hidden_c = _hidden_c;
        A_hidden_c_done = true;
        done_A_2 = true;
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
    bool public B_c;
    bool public B_c_done;
    bool public done_B_3;
    function yield_B3(bool _c) public by(Role.B) at_step(3) {
        require(!done_B_3, "done");
        require(true, "where");
        B_c = _c;
        B_c_done = true;
        done_B_3 = true;
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
    bool public A_c;
    bool public A_c_done;
    bool public done_A_4;
    function reveal_A4(bool _c, uint256 salt) public by(Role.A) at_step(4) {
        require(!done_A_4, "done");
        require(keccak256(abi.encodePacked(_c, salt)) == bytes32(A_hidden_c), "bad reveal");
        require(true, "where");
        A_c = _c;
        A_c_done = true;
        done_A_4 = true;
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
    function withdraw_5_A() public by(Role.A) at_step(5) {
        int256 delta = ((((A_c != B_c) || ! B_c_done)) ? int256(1) : (- int256(1)));
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
    function withdraw_5_B() public by(Role.B) at_step(5) {
        int256 delta = ((((A_c == B_c) || ! A_c_done)) ? int256(1) : (- int256(1)));
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
