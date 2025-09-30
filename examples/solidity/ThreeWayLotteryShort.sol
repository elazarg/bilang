
pragma solidity ^0.8.31;
contract ThreeWayLotteryShort {
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
    enum Role { None, Issuer, Alice, Bob }
    mapping(address => Role) public role;
    mapping(address => uint256) public balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r, "bad role");
        _;
    }
    // step 0
    mapping(address => bytes32) private commitsIssuer;
    mapping(address => uint256) private timesIssuer;
    bool public halfStepIssuer;
    function join_commit_Issuer(bytes32 c) public at_step(0) {
        require(commitsIssuer[msg.sender] == bytes32(0), "already committed");
        require(!halfStepIssuer, "half step passed");
        commitsIssuer[msg.sender] = c;
        timesIssuer[msg.sender] = block.timestamp;
    }
    event BroadcastHalfIssuer();
    function __nextHalfStepIssuer() public at_step(0) {
        require(block.timestamp >= lastTs + STEP_TIME, "too soon");
        require(halfStepIssuer == false, "already advanced");
        emit BroadcastHalfIssuer();
        halfStepIssuer = true;
        lastTs = block.timestamp;
    }
    int256 public Issuer_c;
    bool public Issuer_c_done;
    function join_Issuer(int256 _c, uint256 salt) public payable at_step(0) {
        require(keccak256(abi.encodePacked(_c, salt)) == commitsIssuer[msg.sender], "bad reveal");
        role[msg.sender] = Role.Issuer;
        require(msg.value == 10, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        Issuer_c = _c;
        Issuer_c_done = true;
    }
    mapping(address => bytes32) private commitsAlice;
    mapping(address => uint256) private timesAlice;
    bool public halfStepAlice;
    function join_commit_Alice(bytes32 c) public at_step(0) {
        require(commitsAlice[msg.sender] == bytes32(0), "already committed");
        require(!halfStepAlice, "half step passed");
        commitsAlice[msg.sender] = c;
        timesAlice[msg.sender] = block.timestamp;
    }
    event BroadcastHalfAlice();
    function __nextHalfStepAlice() public at_step(0) {
        require(block.timestamp >= lastTs + STEP_TIME, "too soon");
        require(halfStepAlice == false, "already advanced");
        emit BroadcastHalfAlice();
        halfStepAlice = true;
        lastTs = block.timestamp;
    }
    int256 public Alice_c;
    bool public Alice_c_done;
    function join_Alice(int256 _c, uint256 salt) public payable at_step(0) {
        require(keccak256(abi.encodePacked(_c, salt)) == commitsAlice[msg.sender], "bad reveal");
        role[msg.sender] = Role.Alice;
        require(msg.value == 10, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        Alice_c = _c;
        Alice_c_done = true;
    }
    mapping(address => bytes32) private commitsBob;
    mapping(address => uint256) private timesBob;
    bool public halfStepBob;
    function join_commit_Bob(bytes32 c) public at_step(0) {
        require(commitsBob[msg.sender] == bytes32(0), "already committed");
        require(!halfStepBob, "half step passed");
        commitsBob[msg.sender] = c;
        timesBob[msg.sender] = block.timestamp;
    }
    event BroadcastHalfBob();
    function __nextHalfStepBob() public at_step(0) {
        require(block.timestamp >= lastTs + STEP_TIME, "too soon");
        require(halfStepBob == false, "already advanced");
        emit BroadcastHalfBob();
        halfStepBob = true;
        lastTs = block.timestamp;
    }
    int256 public Bob_c;
    bool public Bob_c_done;
    function join_Bob(int256 _c, uint256 salt) public payable at_step(0) {
        require(keccak256(abi.encodePacked(_c, salt)) == commitsBob[msg.sender], "bad reveal");
        role[msg.sender] = Role.Bob;
        require(msg.value == 10, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        Bob_c = _c;
        Bob_c_done = true;
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
    function withdraw_1_Bob() public by(Role.Bob) at_step(1) {
        int256 delta = (((! Alice_c_done || ! Bob_c_done)) ? (- int256(10)) : ((! Issuer_c_done) ? (- int256(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int256(3)) * int256(3)) == ((Issuer_c + Alice_c) + Bob_c))) ? (- int256(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int256(3)) * int256(3)) == (((Issuer_c + Alice_c) + Bob_c) - int256(1)))) ? int256(20) : (- int256(10))))));
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
    function withdraw_1_Issuer() public by(Role.Issuer) at_step(1) {
        int256 delta = (((! Alice_c_done || ! Bob_c_done)) ? int256(20) : ((! Issuer_c_done) ? (- int256(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int256(3)) * int256(3)) == ((Issuer_c + Alice_c) + Bob_c))) ? (- int256(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int256(3)) * int256(3)) == (((Issuer_c + Alice_c) + Bob_c) - int256(1)))) ? (- int256(10)) : int256(20)))));
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
    function withdraw_1_Alice() public by(Role.Alice) at_step(1) {
        int256 delta = (((! Alice_c_done || ! Bob_c_done)) ? (- int256(10)) : ((! Issuer_c_done) ? int256(20) : (((((((Issuer_c + Alice_c) + Bob_c) / int256(3)) * int256(3)) == ((Issuer_c + Alice_c) + Bob_c))) ? int256(20) : (((((((Issuer_c + Alice_c) + Bob_c) / int256(3)) * int256(3)) == (((Issuer_c + Alice_c) + Bob_c) - int256(1)))) ? (- int256(10)) : (- int256(10))))));
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
