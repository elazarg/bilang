
pragma solidity ^0.8.31;
contract OddsEvens {
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
    enum Role { None, Odd, Even }
    mapping(address => Role) public role;
    mapping(address => uint256) public balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r, "bad role");
        _;
    }
    // step 0
    bool public doneOdd;
    function join_Odd() public payable by(Role.None) at_step(0) {
        require(!doneOdd, "already joined");
        role[msg.sender] = Role.Odd;
        require(msg.value == 100, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        doneOdd = true;
    }
    bool public doneEven;
    function join_Even() public payable by(Role.None) at_step(0) {
        require(!doneEven, "already joined");
        role[msg.sender] = Role.Even;
        require(msg.value == 100, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        doneEven = true;
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
    bool public Odd_c;
    bool public Odd_c_done;
    bool public done_Odd_1;
    function yield_Odd1(bool _c) public by(Role.Odd) at_step(1) {
        require(!done_Odd_1, "done");
        require(true, "where");
        Odd_c = _c;
        Odd_c_done = true;
        done_Odd_1 = true;
    }
    bool public Even_c;
    bool public Even_c_done;
    bool public done_Even_1;
    function yield_Even1(bool _c) public by(Role.Even) at_step(1) {
        require(!done_Even_1, "done");
        require(true, "where");
        Even_c = _c;
        Even_c_done = true;
        done_Even_1 = true;
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
    function withdraw_2_Even() public by(Role.Even) at_step(2) {
        int256 delta = (((Even_c_done && Odd_c_done)) ? (((Even_c == Odd_c)) ? int256(10) : (- int256(10))) : (((! Even_c_done && Odd_c_done)) ? (- int256(100)) : (- int256(100))));
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
    function withdraw_2_Odd() public by(Role.Odd) at_step(2) {
        int256 delta = (((Even_c_done && Odd_c_done)) ? (((Even_c == Odd_c)) ? (- int256(10)) : int256(10)) : (((! Even_c_done && Odd_c_done)) ? int256(10) : (- int256(100))));
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
