pragma solidity ^0.4.22;
contract TicTacToe {
    constructor() public {
        lastBlock = block.timestamp;
    }
    function keccak(bool x, uint salt) pure public returns(bytes32) {
        return keccak256(x, salt);
    }
    // Step
    uint constant STEP_TIME = 500;
    int step;
    uint lastBlock;
    modifier at_step(int _step) {
        require(step == _step);
        //require(block.timestamp < lastBlock + STEP_TIME);
        _;
    }
    // roles
    enum Role { None, X, O }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
    // step 0
    bool doneX;
    function join_X() at_step(0) public by(Role.None) payable {
        require(!doneX);
        role[msg.sender] = Role.X;
        require(msg.value == 100); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneX = true;
    }
    event Broadcast0(); // TODO: add params
    function __nextStep0() public {
        require(step == 0);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast0();
        step = 1;
        lastBlock = block.timestamp;
    }
    // end 0
    // step 1
    bool doneO;
    function join_O() at_step(1) public by(Role.None) payable {
        require(!doneO);
        role[msg.sender] = Role.O;
        require(msg.value == 100); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneO = true;
    }
    event Broadcast1(); // TODO: add params
    function __nextStep1() public {
        require(step == 1);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast1();
        step = 2;
        lastBlock = block.timestamp;
    }
    // end 1
    // step 2
    int X_c1;
    bool X_c1_done;
    bool done_X_2;
    function yield_X2(int _c1) by (Role.X) at_step(2) public {
        require(!done_X_2);
        require(true);
        X_c1 = _c1;
        X_c1_done = true;
        done_X_2 = true;
    }
    event Broadcast2(); // TODO: add params
    function __nextStep2() public {
        require(step == 2);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast2();
        step = 3;
        lastBlock = block.timestamp;
    }
    // end 2
    // step 3
    int O_c1;
    bool O_c1_done;
    bool done_O_3;
    function yield_O3(int _c1) by (Role.O) at_step(3) public {
        require(!done_O_3);
        require(_alldiff(X_c1,O_c1));
        O_c1 = _c1;
        O_c1_done = true;
        done_O_3 = true;
    }
    event Broadcast3(); // TODO: add params
    function __nextStep3() public {
        require(step == 3);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast3();
        step = 4;
        lastBlock = block.timestamp;
    }
    // end 3
    // step 4
    int X_c2;
    bool X_c2_done;
    bool done_X_4;
    function yield_X4(int _c2) by (Role.X) at_step(4) public {
        require(!done_X_4);
        require(_alldiff(X_c1,O_c1,X_c2));
        X_c2 = _c2;
        X_c2_done = true;
        done_X_4 = true;
    }
    event Broadcast4(); // TODO: add params
    function __nextStep4() public {
        require(step == 4);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast4();
        step = 5;
        lastBlock = block.timestamp;
    }
    // end 4
    // step 5
    int O_c2;
    bool O_c2_done;
    bool done_O_5;
    function yield_O5(int _c2) by (Role.O) at_step(5) public {
        require(!done_O_5);
        require(_alldiff(X_c1,O_c1,X_c2,O_c2));
        O_c2 = _c2;
        O_c2_done = true;
        done_O_5 = true;
    }
    event Broadcast5(); // TODO: add params
    function __nextStep5() public {
        require(step == 5);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast5();
        step = 6;
        lastBlock = block.timestamp;
    }
    // end 5
    // step 6
    int X_c3;
    bool X_c3_done;
    bool done_X_6;
    function yield_X6(int _c3) by (Role.X) at_step(6) public {
        require(!done_X_6);
        require(_alldiff(X_c1,O_c1,X_c2,O_c2,X_c3));
        X_c3 = _c3;
        X_c3_done = true;
        done_X_6 = true;
    }
    event Broadcast6(); // TODO: add params
    function __nextStep6() public {
        require(step == 6);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast6();
        step = 7;
        lastBlock = block.timestamp;
    }
    // end 6
    // step 7
    int O_c3;
    bool O_c3_done;
    bool done_O_7;
    function yield_O7(int _c3) by (Role.O) at_step(7) public {
        require(!done_O_7);
        require(_alldiff(X_c1,O_c1,X_c2,O_c2,X_c3,O_c3));
        O_c3 = _c3;
        O_c3_done = true;
        done_O_7 = true;
    }
    event Broadcast7(); // TODO: add params
    function __nextStep7() public {
        require(step == 7);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast7();
        step = 8;
        lastBlock = block.timestamp;
    }
    // end 7
    // step 8
    int X_c4;
    bool X_c4_done;
    bool done_X_8;
    function yield_X8(int _c4) by (Role.X) at_step(8) public {
        require(!done_X_8);
        require(_alldiff(X_c1,O_c1,X_c2,O_c2,X_c3,O_c3,X_c4));
        X_c4 = _c4;
        X_c4_done = true;
        done_X_8 = true;
    }
    event Broadcast8(); // TODO: add params
    function __nextStep8() public {
        require(step == 8);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast8();
        step = 9;
        lastBlock = block.timestamp;
    }
    // end 8
    // step 9
    int O_c4;
    bool O_c4_done;
    bool done_O_9;
    function yield_O9(int _c4) by (Role.O) at_step(9) public {
        require(!done_O_9);
        require(_alldiff(X_c1,O_c1,X_c2,O_c2,X_c3,O_c3,X_c4,O_c4));
        O_c4 = _c4;
        O_c4_done = true;
        done_O_9 = true;
    }
    event Broadcast9(); // TODO: add params
    function __nextStep9() public {
        require(step == 9);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast9();
        step = 10;
        lastBlock = block.timestamp;
    }
    // end 9
    function withdraw_10_X() by(Role.X) at_step(10) public {
        int amount = int(0);
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_10_O() by(Role.O) at_step(10) public {
        int amount = int(0);
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
