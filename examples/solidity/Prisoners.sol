
pragma solidity ^0.8.31;
contract Prisoners {
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
        require(msg.value == 100, "bad stake"); balanceOf[msg.sender] = msg.value;
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
        require(msg.value == 100, "bad stake"); balanceOf[msg.sender] = msg.value;
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
    bool public A_c;
    bool public A_c_done;
    bool public done_A_2;
    function yield_A2(bool _c) public by(Role.A) at_step(2) {
        require(!done_A_2, "done");
        require(true, "where");
        A_c = _c;
        A_c_done = true;
        done_A_2 = true;
    }
    bool public B_c;
    bool public B_c_done;
    bool public done_B_2;
    function yield_B2(bool _c) public by(Role.B) at_step(2) {
        require(!done_B_2, "done");
        require(true, "where");
        B_c = _c;
        B_c_done = true;
        done_B_2 = true;
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
    function withdraw_3_A() public by(Role.A) at_step(3) {
        int256 delta = (((A_c_done && B_c_done)) ? (((A_c && B_c)) ? (- int256(2)) : (((A_c && (! B_c))) ? int256(0) : ((((! A_c) && B_c)) ? (- int256(3)) : (- int256(1))))) : ((! A_c_done) ? (- int256(100)) : int256(10)));
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
    function withdraw_3_B() public by(Role.B) at_step(3) {
        int256 delta = (((A_c_done && B_c_done)) ? (((A_c && B_c)) ? (- int256(2)) : (((A_c && (! B_c))) ? (- int256(3)) : ((((! A_c) && B_c)) ? int256(0) : (- int256(1))))) : ((! A_c_done) ? int256(10) : (- int256(100))));
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
