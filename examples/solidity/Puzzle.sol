
pragma solidity ^0.8.31;
contract Puzzle {
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
    enum Role { None, Q, A }
    mapping(address => Role) public role;
    mapping(address => uint256) public balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r, "bad role");
        _;
    }
    // step 0
    mapping(address => bytes32) private commitsQ;
    mapping(address => uint256) private timesQ;
    bool public halfStepQ;
    function join_commit_Q(bytes32 c) public at_step(0) {
        require(commitsQ[msg.sender] == bytes32(0), "already committed");
        require(!halfStepQ, "half step passed");
        commitsQ[msg.sender] = c;
        timesQ[msg.sender] = block.timestamp;
    }
    event BroadcastHalfQ();
    function __nextHalfStepQ() public at_step(0) {
        require(block.timestamp >= lastTs + STEP_TIME, "too soon");
        require(halfStepQ == false, "already advanced");
        emit BroadcastHalfQ();
        halfStepQ = true;
        lastTs = block.timestamp;
    }
    int256 public Q_x;
    bool public Q_x_done;
    function join_Q(int256 _x, uint256 salt) public payable at_step(0) {
        require(keccak256(abi.encodePacked(_x, salt)) == commitsQ[msg.sender], "bad reveal");
        role[msg.sender] = Role.Q;
        require(msg.value == 50, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        Q_x = _x;
        Q_x_done = true;
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
    mapping(address => bytes32) private commitsA;
    mapping(address => uint256) private timesA;
    bool public halfStepA;
    function join_commit_A(bytes32 c) public at_step(1) {
        require(commitsA[msg.sender] == bytes32(0), "already committed");
        require(!halfStepA, "half step passed");
        commitsA[msg.sender] = c;
        timesA[msg.sender] = block.timestamp;
    }
    event BroadcastHalfA();
    function __nextHalfStepA() public at_step(1) {
        require(block.timestamp >= lastTs + STEP_TIME, "too soon");
        require(halfStepA == false, "already advanced");
        emit BroadcastHalfA();
        halfStepA = true;
        lastTs = block.timestamp;
    }
    int256 public A_p;
    int256 public A_q;
    bool public A_p_done;
    bool public A_q_done;
    function join_A(int256 _p, int256 _q, uint256 salt) public at_step(1) {
        require(keccak256(abi.encodePacked(_p, _q, salt)) == commitsA[msg.sender], "bad reveal");
        role[msg.sender] = Role.A;
        balanceOf[msg.sender] = msg.value;
        require(((((A_p * A_q) == Q_x) && (A_p != int256(1))) && (A_q != int256(1))), "where");
        A_p = _p;
        A_q = _q;
        A_p_done = true;
        A_q_done = true;
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
    function withdraw_2_Q() public by(Role.Q) at_step(2) {
        int256 delta = int256(0);
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
    function withdraw_2_A() public by(Role.A) at_step(2) {
        int256 delta = int256(50);
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
