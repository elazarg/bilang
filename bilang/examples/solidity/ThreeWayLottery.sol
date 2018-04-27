pragma solidity ^0.4.22;
contract ThreeWayLottery {
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
    enum Role { None, Issuer, Alice, Bob }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
    // step 0
    bool doneIssuer;
    function join_Issuer() at_step(0) public by(Role.None) payable {
        require(!doneIssuer);
        role[msg.sender] = Role.Issuer;
        require(msg.value == 10); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneIssuer = true;
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
    bool doneAlice;
    function join_Alice() at_step(1) public by(Role.None) payable {
        require(!doneAlice);
        role[msg.sender] = Role.Alice;
        require(msg.value == 10); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneAlice = true;
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
    bool doneBob;
    function join_Bob() at_step(2) public by(Role.None) payable {
        require(!doneBob);
        role[msg.sender] = Role.Bob;
        require(msg.value == 10); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneBob = true;
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
    int Issuer_c;
    bool Issuer_c_done;
    bool done_Issuer_3;
    function yield_Issuer3(int _c) by (Role.Issuer) at_step(3) public {
        require(!done_Issuer_3);
        require(true);
        Issuer_c = _c;
        Issuer_c_done = true;
        done_Issuer_3 = true;
    }
    int Alice_c;
    bool Alice_c_done;
    bool done_Alice_3;
    function yield_Alice3(int _c) by (Role.Alice) at_step(3) public {
        require(!done_Alice_3);
        require(true);
        Alice_c = _c;
        Alice_c_done = true;
        done_Alice_3 = true;
    }
    int Bob_c;
    bool Bob_c_done;
    bool done_Bob_3;
    function yield_Bob3(int _c) by (Role.Bob) at_step(3) public {
        require(!done_Bob_3);
        require(true);
        Bob_c = _c;
        Bob_c_done = true;
        done_Bob_3 = true;
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
    function withdraw_4_Bob() by(Role.Bob) at_step(4) public {
        int amount = (((! Alice_c_done || ! Bob_c_done)) ? (- int(10)) : ((! Issuer_c_done) ? (- int(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == ((Issuer_c + Alice_c) + Bob_c))) ? (- int(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == (((Issuer_c + Alice_c) + Bob_c) - int(1)))) ? int(20) : (- int(10))))));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_4_Issuer() by(Role.Issuer) at_step(4) public {
        int amount = (((! Alice_c_done || ! Bob_c_done)) ? int(20) : ((! Issuer_c_done) ? (- int(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == ((Issuer_c + Alice_c) + Bob_c))) ? (- int(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == (((Issuer_c + Alice_c) + Bob_c) - int(1)))) ? (- int(10)) : int(20)))));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_4_Alice() by(Role.Alice) at_step(4) public {
        int amount = (((! Alice_c_done || ! Bob_c_done)) ? (- int(10)) : ((! Issuer_c_done) ? int(20) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == ((Issuer_c + Alice_c) + Bob_c))) ? int(20) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == (((Issuer_c + Alice_c) + Bob_c) - int(1)))) ? (- int(10)) : (- int(10))))));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
