pragma solidity ^0.4.22;
contract ThreeWayLotteryShort {
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
    mapping(address => bytes32) commitsIssuer;
    mapping(address => uint) timesIssuer;
    bool halfStepIssuer;
    function join_commit_Issuer(bytes32 c) at_step(0) public {
        require(commitsIssuer[msg.sender] == bytes32(0));
        require(!halfStepIssuer);
        commitsIssuer[msg.sender] = c;
        timesIssuer[msg.sender] = block.timestamp;
    }
    event BroadcastHalfIssuer();
    function __nextHalfStepIssuer() at_step(0) public {
        require(block.timestamp >= lastBlock + STEP_TIME);
        require(halfStepIssuer == false);
        emit BroadcastHalfIssuer();
        halfStepIssuer = true;
        lastBlock = block.timestamp;
    }
    address chosenRoleIssuer;
    int Issuer_c;
    bool Issuer_c_done;
    function join_Issuer(int _c, uint salt) at_step(0) public payable {
        require(keccak256(_c, salt) == bytes32(commitsIssuer[msg.sender]));
        if (chosenRoleIssuer != address(0x0))
             require(timesIssuer[msg.sender] < timesIssuer[chosenRoleIssuer]);
        role[msg.sender] = Role.Issuer;
        require(msg.value == 10); 
        balanceOf[msg.sender] = msg.value;
        chosenRoleIssuer = msg.sender;
        require(true);
        Issuer_c = _c;
        Issuer_c_done = true;
    }
    mapping(address => bytes32) commitsAlice;
    mapping(address => uint) timesAlice;
    bool halfStepAlice;
    function join_commit_Alice(bytes32 c) at_step(0) public {
        require(commitsAlice[msg.sender] == bytes32(0));
        require(!halfStepAlice);
        commitsAlice[msg.sender] = c;
        timesAlice[msg.sender] = block.timestamp;
    }
    event BroadcastHalfAlice();
    function __nextHalfStepAlice() at_step(0) public {
        require(block.timestamp >= lastBlock + STEP_TIME);
        require(halfStepAlice == false);
        emit BroadcastHalfAlice();
        halfStepAlice = true;
        lastBlock = block.timestamp;
    }
    address chosenRoleAlice;
    int Alice_c;
    bool Alice_c_done;
    function join_Alice(int _c, uint salt) at_step(0) public payable {
        require(keccak256(_c, salt) == bytes32(commitsAlice[msg.sender]));
        if (chosenRoleAlice != address(0x0))
             require(timesAlice[msg.sender] < timesAlice[chosenRoleAlice]);
        role[msg.sender] = Role.Alice;
        require(msg.value == 10); 
        balanceOf[msg.sender] = msg.value;
        chosenRoleAlice = msg.sender;
        require(true);
        Alice_c = _c;
        Alice_c_done = true;
    }
    mapping(address => bytes32) commitsBob;
    mapping(address => uint) timesBob;
    bool halfStepBob;
    function join_commit_Bob(bytes32 c) at_step(0) public {
        require(commitsBob[msg.sender] == bytes32(0));
        require(!halfStepBob);
        commitsBob[msg.sender] = c;
        timesBob[msg.sender] = block.timestamp;
    }
    event BroadcastHalfBob();
    function __nextHalfStepBob() at_step(0) public {
        require(block.timestamp >= lastBlock + STEP_TIME);
        require(halfStepBob == false);
        emit BroadcastHalfBob();
        halfStepBob = true;
        lastBlock = block.timestamp;
    }
    address chosenRoleBob;
    int Bob_c;
    bool Bob_c_done;
    function join_Bob(int _c, uint salt) at_step(0) public payable {
        require(keccak256(_c, salt) == bytes32(commitsBob[msg.sender]));
        if (chosenRoleBob != address(0x0))
             require(timesBob[msg.sender] < timesBob[chosenRoleBob]);
        role[msg.sender] = Role.Bob;
        require(msg.value == 10); 
        balanceOf[msg.sender] = msg.value;
        chosenRoleBob = msg.sender;
        require(true);
        Bob_c = _c;
        Bob_c_done = true;
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
    function withdraw_1_Bob() by(Role.Bob) at_step(1) public {
        int amount;
        amount = (((! Alice_c_done || ! Bob_c_done)) ? (- int(10)) : ((! Issuer_c_done) ? (- int(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == ((Issuer_c + Alice_c) + Bob_c))) ? (- int(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == (((Issuer_c + Alice_c) + Bob_c) - int(1)))) ? int(20) : (- int(10))))));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_1_Issuer() by(Role.Issuer) at_step(1) public {
        int amount;
        amount = (((! Alice_c_done || ! Bob_c_done)) ? int(20) : ((! Issuer_c_done) ? (- int(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == ((Issuer_c + Alice_c) + Bob_c))) ? (- int(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == (((Issuer_c + Alice_c) + Bob_c) - int(1)))) ? (- int(10)) : int(20)))));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_1_Alice() by(Role.Alice) at_step(1) public {
        int amount;
        amount = (((! Alice_c_done || ! Bob_c_done)) ? (- int(10)) : ((! Issuer_c_done) ? int(20) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == ((Issuer_c + Alice_c) + Bob_c))) ? int(20) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == (((Issuer_c + Alice_c) + Bob_c) - int(1)))) ? (- int(10)) : (- int(10))))));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
