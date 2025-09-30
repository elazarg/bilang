
pragma solidity ^0.8.31;
contract OddsEvensShort {
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
    mapping(address => bytes32) private commitsOdd;
    mapping(address => uint256) private timesOdd;
    bool public halfStepOdd;
    function join_commit_Odd(bytes32 c) public at_step(0) {
        require(commitsOdd[msg.sender] == bytes32(0), "already committed");
        require(!halfStepOdd, "half step passed");
        commitsOdd[msg.sender] = c;
        timesOdd[msg.sender] = block.timestamp;
    }
    event BroadcastHalfOdd();
    function __nextHalfStepOdd() public at_step(0) {
        require(block.timestamp >= lastTs + STEP_TIME, "too soon");
        require(halfStepOdd == false, "already advanced");
        emit BroadcastHalfOdd();
        halfStepOdd = true;
        lastTs = block.timestamp;
    }
    bool public Odd_c;
    bool public Odd_c_done;
    function join_Odd(bool _c, uint256 salt) public payable at_step(0) {
        require(keccak256(abi.encodePacked(_c, salt)) == commitsOdd[msg.sender], "bad reveal");
        role[msg.sender] = Role.Odd;
        require(msg.value == 100, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        Odd_c = _c;
        Odd_c_done = true;
    }
    mapping(address => bytes32) private commitsEven;
    mapping(address => uint256) private timesEven;
    bool public halfStepEven;
    function join_commit_Even(bytes32 c) public at_step(0) {
        require(commitsEven[msg.sender] == bytes32(0), "already committed");
        require(!halfStepEven, "half step passed");
        commitsEven[msg.sender] = c;
        timesEven[msg.sender] = block.timestamp;
    }
    event BroadcastHalfEven();
    function __nextHalfStepEven() public at_step(0) {
        require(block.timestamp >= lastTs + STEP_TIME, "too soon");
        require(halfStepEven == false, "already advanced");
        emit BroadcastHalfEven();
        halfStepEven = true;
        lastTs = block.timestamp;
    }
    bool public Even_c;
    bool public Even_c_done;
    function join_Even(bool _c, uint256 salt) public payable at_step(0) {
        require(keccak256(abi.encodePacked(_c, salt)) == commitsEven[msg.sender], "bad reveal");
        role[msg.sender] = Role.Even;
        require(msg.value == 100, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        Even_c = _c;
        Even_c_done = true;
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
    function withdraw_1_Even() public by(Role.Even) at_step(1) {
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
    function withdraw_1_Odd() public by(Role.Odd) at_step(1) {
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
