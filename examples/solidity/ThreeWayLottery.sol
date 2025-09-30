
pragma solidity ^0.8.31;
contract ThreeWayLottery {
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
    bool public doneIssuer;
    function join_Issuer() public payable by(Role.None) at_step(0) {
        require(!doneIssuer, "already joined");
        role[msg.sender] = Role.Issuer;
        require(msg.value == 10, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        doneIssuer = true;
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
    bool public doneAlice;
    function join_Alice() public payable by(Role.None) at_step(1) {
        require(!doneAlice, "already joined");
        role[msg.sender] = Role.Alice;
        require(msg.value == 10, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        doneAlice = true;
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
    bool public doneBob;
    function join_Bob() public payable by(Role.None) at_step(2) {
        require(!doneBob, "already joined");
        role[msg.sender] = Role.Bob;
        require(msg.value == 10, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        doneBob = true;
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
    int256 public Issuer_c;
    bool public Issuer_c_done;
    bool public done_Issuer_3;
    function yield_Issuer3(int256 _c) public by(Role.Issuer) at_step(3) {
        require(!done_Issuer_3, "done");
        require(true, "where");
        Issuer_c = _c;
        Issuer_c_done = true;
        done_Issuer_3 = true;
    }
    int256 public Alice_c;
    bool public Alice_c_done;
    bool public done_Alice_3;
    function yield_Alice3(int256 _c) public by(Role.Alice) at_step(3) {
        require(!done_Alice_3, "done");
        require(true, "where");
        Alice_c = _c;
        Alice_c_done = true;
        done_Alice_3 = true;
    }
    int256 public Bob_c;
    bool public Bob_c_done;
    bool public done_Bob_3;
    function yield_Bob3(int256 _c) public by(Role.Bob) at_step(3) {
        require(!done_Bob_3, "done");
        require(true, "where");
        Bob_c = _c;
        Bob_c_done = true;
        done_Bob_3 = true;
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
    function withdraw_4_Bob() public by(Role.Bob) at_step(4) {
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
    function withdraw_4_Issuer() public by(Role.Issuer) at_step(4) {
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
    function withdraw_4_Alice() public by(Role.Alice) at_step(4) {
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
