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
    function join_Odd() at_step(0) public payable {
        role[msg.sender] = Role.Odd;
        require(msg.value == 100); 
        require(!doneOdd);
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
    function join_Even() at_step(1) public payable {
        role[msg.sender] = Role.Even;
        require(msg.value == 100); 
        require(!doneEven);
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
        bool freshVar23;
        {
        bool freshVar24;
        {
        bool freshVar25;
        freshVar25 = Even_c_done;
        freshVar24 = ! freshVar25;
        }
        bool freshVar26;
        {
        bool freshVar27;
        freshVar27 = Odd_c_done;
        freshVar26 = ! freshVar27;
        }
        freshVar23 = freshVar24 && freshVar26;
        }
        if (freshVar23) { 
        amount = (((Even_c == Odd_c)) ? int(10) : (- int(10)));
        } else {
        bool freshVar28;
        {
        bool freshVar29;
        freshVar29 = Even_c_done;
        bool freshVar30;
        {
        bool freshVar31;
        freshVar31 = Odd_c_done;
        freshVar30 = ! freshVar31;
        }
        freshVar28 = freshVar29 && freshVar30;
        }
        if (freshVar28) { 
        amount = (- int(100));
        } else {
        amount = (- int(100));
        }
        }
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_3_Odd() by(Role.Odd) at_step(3) public {
        int amount;
        bool freshVar32;
        {
        bool freshVar33;
        {
        bool freshVar34;
        freshVar34 = Even_c_done;
        freshVar33 = ! freshVar34;
        }
        bool freshVar35;
        {
        bool freshVar36;
        freshVar36 = Odd_c_done;
        freshVar35 = ! freshVar36;
        }
        freshVar32 = freshVar33 && freshVar35;
        }
        if (freshVar32) { 
        amount = (((Even_c == Odd_c)) ? (- int(10)) : int(10));
        } else {
        bool freshVar37;
        {
        bool freshVar38;
        freshVar38 = Even_c_done;
        bool freshVar39;
        {
        bool freshVar40;
        freshVar40 = Odd_c_done;
        freshVar39 = ! freshVar40;
        }
        freshVar37 = freshVar38 && freshVar39;
        }
        if (freshVar37) { 
        amount = int(10);
        } else {
        amount = (- int(100));
        }
        }
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
