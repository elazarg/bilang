pragma solidity ^0.4.22;
contract Prisoners {
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
    enum Role { None, A, B }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
    // step 0
    bool doneA;
    function join_A() at_step(0) public by(Role.None) payable {
        require(!doneA);
        role[msg.sender] = Role.A;
        require(msg.value == 100); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneA = true;
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
    bool doneB;
    function join_B() at_step(1) public by(Role.None) payable {
        require(!doneB);
        role[msg.sender] = Role.B;
        require(msg.value == 100); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneB = true;
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
    bool A_c;
    bool A_c_done;
    bool done_A_2;
    function yield_A2(bool _c) by (Role.A) at_step(2) public {
        require(!done_A_2);
        require(true);
        A_c = _c;
        A_c_done = true;
        done_A_2 = true;
    }
    bool B_c;
    bool B_c_done;
    bool done_B_2;
    function yield_B2(bool _c) by (Role.B) at_step(2) public {
        require(!done_B_2);
        require(true);
        B_c = _c;
        B_c_done = true;
        done_B_2 = true;
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
    function withdraw_3_A() by(Role.A) at_step(3) public {
        int amount;
        amount = ((((! ! A_c_done) && (! ! B_c_done))) ? (((A_c && B_c)) ? (- int(2)) : (((A_c && (! B_c))) ? int(0) : ((((! A_c) && B_c)) ? (- int(3)) : (- int(1))))) : ((! A_c_done) ? (- int(100)) : int(10)));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_3_B() by(Role.B) at_step(3) public {
        int amount;
        amount = ((((! ! A_c_done) && (! ! B_c_done))) ? (((A_c && B_c)) ? (- int(2)) : (((A_c && (! B_c))) ? (- int(3)) : ((((! A_c) && B_c)) ? int(0) : (- int(1))))) : ((! A_c_done) ? int(10) : (- int(100))));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
