pragma solidity ^0.4.22;
contract OddsEvens {
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
    enum Role { None, Odd, Even }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
    // step 0
    bool doneOdd;
    function join_Odd() at_step(0) public by(Role.None) payable {
        require(!doneOdd);
        role[msg.sender] = Role.Odd;
        require(msg.value == 100); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneOdd = true;
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
    bool doneEven;
    function join_Even() at_step(1) public by(Role.None) payable {
        require(!doneEven);
        role[msg.sender] = Role.Even;
        require(msg.value == 100); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneEven = true;
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
    bool Odd_c;
    bool Odd_c_done;
    bool done_Odd_2;
    function yield_Odd2(bool _c) by (Role.Odd) at_step(2) public {
        require(!done_Odd_2);
        require(true);
        Odd_c = _c;
        Odd_c_done = true;
        done_Odd_2 = true;
    }
    bool Even_c;
    bool Even_c_done;
    bool done_Even_2;
    function yield_Even2(bool _c) by (Role.Even) at_step(2) public {
        require(!done_Even_2);
        require(true);
        Even_c = _c;
        Even_c_done = true;
        done_Even_2 = true;
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
    function withdraw_3_Even() by(Role.Even) at_step(3) public {
        int amount;
        amount = ((((! ! Even_c_done) && (! ! Odd_c_done))) ? (((Even_c == Odd_c)) ? int(10) : (- int(10))) : (((! Even_c_done && (! ! Odd_c_done))) ? (- int(100)) : (- int(100))));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_3_Odd() by(Role.Odd) at_step(3) public {
        int amount;
        amount = ((((! ! Even_c_done) && (! ! Odd_c_done))) ? (((Even_c == Odd_c)) ? (- int(10)) : int(10)) : (((! Even_c_done && (! ! Odd_c_done))) ? int(10) : (- int(100))));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
