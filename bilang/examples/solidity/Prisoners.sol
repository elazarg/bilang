pragma solidity ^0.4.22;
contract Prisoners {
    constructor() public {
        lastBlock = block.timestamp;
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
    function join_A() at_step(0) public payable {
        role[msg.sender] = Role.A;
        require(msg.value == 100);
        require(!doneA);
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
    function join_B() at_step(1) public payable {
        role[msg.sender] = Role.B;
        require(msg.value == 100);
        require(!doneB);
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
    function yield_A2(bool _c) at_step(2) public {
        require(role[msg.sender] == Role.A);
        require(!done_A_2);
        require(true);
        A_c = _c;
        A_c_done = true;
        done_A_2 = true;
    }
    bool B_c;
    bool B_c_done;
    bool done_B_2;
    function yield_B2(bool _c) at_step(2) public {
        require(role[msg.sender] == Role.B);
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
    function withdraw_3_A() by(Role.A) public at_step(3) {
        require(role[msg.sender] == Role.A);
        int amount;
        bool freshVar59;
        {
        bool freshVar60;
        {
        bool freshVar61;
        freshVar61 = A_c_done;
        freshVar60 = ! freshVar61;
        }
        bool freshVar62;
        {
        bool freshVar63;
        freshVar63 = B_c_done;
        freshVar62 = ! freshVar63;
        }
        freshVar59 = freshVar60 && freshVar62;
        }
        if (freshVar59) { 
        amount = (((A_c && B_c)) ? (- int(2)) : (((A_c && (! B_c))) ? int(0) : ((((! A_c) && B_c)) ? (- int(3)) : (- int(1)))));
        } else {
        bool freshVar64;
        freshVar64 = A_c_done;
        if (freshVar64) { 
        amount = (- int(100));
        } else {
        amount = int(10);
        }
        }
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_3_B() by(Role.B) public at_step(3) {
        require(role[msg.sender] == Role.B);
        int amount;
        bool freshVar65;
        {
        bool freshVar66;
        {
        bool freshVar67;
        freshVar67 = A_c_done;
        freshVar66 = ! freshVar67;
        }
        bool freshVar68;
        {
        bool freshVar69;
        freshVar69 = B_c_done;
        freshVar68 = ! freshVar69;
        }
        freshVar65 = freshVar66 && freshVar68;
        }
        if (freshVar65) { 
        amount = (((A_c && B_c)) ? (- int(2)) : (((A_c && (! B_c))) ? (- int(3)) : ((((! A_c) && B_c)) ? int(0) : (- int(1)))));
        } else {
        bool freshVar70;
        freshVar70 = A_c_done;
        if (freshVar70) { 
        amount = int(10);
        } else {
        amount = (- int(100));
        }
        }
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
