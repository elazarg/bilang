
pragma solidity ^0.8.31;
contract TicTacToe {
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
    enum Role { None, X, O }
    mapping(address => Role) public role;
    mapping(address => uint256) public balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r, "bad role");
        _;
    }
    // step 0
    bool public doneX;
    function join_X() public payable by(Role.None) at_step(0) {
        require(!doneX, "already joined");
        role[msg.sender] = Role.X;
        require(msg.value == 100, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        doneX = true;
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
    bool public doneO;
    function join_O() public payable by(Role.None) at_step(1) {
        require(!doneO, "already joined");
        role[msg.sender] = Role.O;
        require(msg.value == 100, "bad stake"); balanceOf[msg.sender] = msg.value;
        require(true, "where");
        doneO = true;
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
    int256 public X_c1;
    bool public X_c1_done;
    bool public done_X_2;
    function yield_X2(int256 _c1) public by(Role.X) at_step(2) {
        require(!done_X_2, "done");
        require(true, "where");
        X_c1 = _c1;
        X_c1_done = true;
        done_X_2 = true;
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
    int256 public O_c1;
    bool public O_c1_done;
    bool public done_O_3;
    function yield_O3(int256 _c1) public by(Role.O) at_step(3) {
        require(!done_O_3, "done");
        require(_alldiff(X_c1,O_c1), "where");
        O_c1 = _c1;
        O_c1_done = true;
        done_O_3 = true;
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
    int256 public X_c2;
    bool public X_c2_done;
    bool public done_X_4;
    function yield_X4(int256 _c2) public by(Role.X) at_step(4) {
        require(!done_X_4, "done");
        require(_alldiff(X_c1,O_c1,X_c2), "where");
        X_c2 = _c2;
        X_c2_done = true;
        done_X_4 = true;
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
    // step 5
    int256 public O_c2;
    bool public O_c2_done;
    bool public done_O_5;
    function yield_O5(int256 _c2) public by(Role.O) at_step(5) {
        require(!done_O_5, "done");
        require(_alldiff(X_c1,O_c1,X_c2,O_c2), "where");
        O_c2 = _c2;
        O_c2_done = true;
        done_O_5 = true;
    }
    event Broadcast5(); // TODO: add params
    function __nextStep5() public {
        require(step == 5, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast5();
        step = 6;
        lastTs = block.timestamp;
    }
    // end 5
    // step 6
    int256 public X_c3;
    bool public X_c3_done;
    bool public done_X_6;
    function yield_X6(int256 _c3) public by(Role.X) at_step(6) {
        require(!done_X_6, "done");
        require(_alldiff(X_c1,O_c1,X_c2,O_c2,X_c3), "where");
        X_c3 = _c3;
        X_c3_done = true;
        done_X_6 = true;
    }
    event Broadcast6(); // TODO: add params
    function __nextStep6() public {
        require(step == 6, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast6();
        step = 7;
        lastTs = block.timestamp;
    }
    // end 6
    // step 7
    int256 public O_c3;
    bool public O_c3_done;
    bool public done_O_7;
    function yield_O7(int256 _c3) public by(Role.O) at_step(7) {
        require(!done_O_7, "done");
        require(_alldiff(X_c1,O_c1,X_c2,O_c2,X_c3,O_c3), "where");
        O_c3 = _c3;
        O_c3_done = true;
        done_O_7 = true;
    }
    event Broadcast7(); // TODO: add params
    function __nextStep7() public {
        require(step == 7, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast7();
        step = 8;
        lastTs = block.timestamp;
    }
    // end 7
    // step 8
    int256 public X_c4;
    bool public X_c4_done;
    bool public done_X_8;
    function yield_X8(int256 _c4) public by(Role.X) at_step(8) {
        require(!done_X_8, "done");
        require(_alldiff(X_c1,O_c1,X_c2,O_c2,X_c3,O_c3,X_c4), "where");
        X_c4 = _c4;
        X_c4_done = true;
        done_X_8 = true;
    }
    event Broadcast8(); // TODO: add params
    function __nextStep8() public {
        require(step == 8, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast8();
        step = 9;
        lastTs = block.timestamp;
    }
    // end 8
    // step 9
    int256 public O_c4;
    bool public O_c4_done;
    bool public done_O_9;
    function yield_O9(int256 _c4) public by(Role.O) at_step(9) {
        require(!done_O_9, "done");
        require(_alldiff(X_c1,O_c1,X_c2,O_c2,X_c3,O_c3,X_c4,O_c4), "where");
        O_c4 = _c4;
        O_c4_done = true;
        done_O_9 = true;
    }
    event Broadcast9(); // TODO: add params
    function __nextStep9() public {
        require(step == 9, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast9();
        step = 10;
        lastTs = block.timestamp;
    }
    // end 9
    function withdraw_10_X() public by(Role.X) at_step(10) {
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
    function withdraw_10_O() public by(Role.O) at_step(10) {
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
    // Reject stray ETH by default
    receive() external payable {
        revert("direct ETH not allowed");
    }
}
