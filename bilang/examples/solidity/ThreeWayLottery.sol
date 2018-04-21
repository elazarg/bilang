pragma solidity ^0.4.22;
contract ThreeWayLottery {
    // roles
    enum Role { None, Issuer, Alice, Bob }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
    // Step
    uint constant STEP_TIME = 500;
    int step;
    uint __lastStep;
    modifier at_step(int _step) {
        require(step == _step);
        require(block.timestamp < __lastStep + STEP_TIME);
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
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepIssuer == false);
        emit BroadcastHalfIssuer();
        halfStepIssuer = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleIssuer;
    function join_Issuer(uint salt) at_step(0) public payable {
        require(keccak256(salt) == bytes32(commitsIssuer[msg.sender]));
        if (chosenRoleIssuer != address(0x0))
             require(timesIssuer[msg.sender] < timesIssuer[chosenRoleIssuer]);
        role[msg.sender] = Role.Issuer;
        balanceOf[msg.sender] = msg.value;
        chosenRoleIssuer = msg.sender;
        require(true);
    }
    event Broadcast0(); // TODO: add params
    function __nextStep0() at_step(0) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast0();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 0
    // step 1
    mapping(address => bytes32) commitsAlice;
    mapping(address => uint) timesAlice;
    bool halfStepAlice;
    function join_commit_Alice(bytes32 c) at_step(1) public {
        require(commitsAlice[msg.sender] == bytes32(0));
        require(!halfStepAlice);
        commitsAlice[msg.sender] = c;
        timesAlice[msg.sender] = block.timestamp;
    }
    event BroadcastHalfAlice();
    function __nextHalfStepAlice() at_step(1) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepAlice == false);
        emit BroadcastHalfAlice();
        halfStepAlice = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleAlice;
    function join_Alice(uint salt) at_step(1) public payable {
        require(keccak256(salt) == bytes32(commitsAlice[msg.sender]));
        if (chosenRoleAlice != address(0x0))
             require(timesAlice[msg.sender] < timesAlice[chosenRoleAlice]);
        role[msg.sender] = Role.Alice;
        balanceOf[msg.sender] = msg.value;
        chosenRoleAlice = msg.sender;
        require(true);
    }
    event Broadcast1(); // TODO: add params
    function __nextStep1() at_step(1) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast1();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 1
    // step 2
    mapping(address => bytes32) commitsBob;
    mapping(address => uint) timesBob;
    bool halfStepBob;
    function join_commit_Bob(bytes32 c) at_step(2) public {
        require(commitsBob[msg.sender] == bytes32(0));
        require(!halfStepBob);
        commitsBob[msg.sender] = c;
        timesBob[msg.sender] = block.timestamp;
    }
    event BroadcastHalfBob();
    function __nextHalfStepBob() at_step(2) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepBob == false);
        emit BroadcastHalfBob();
        halfStepBob = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleBob;
    function join_Bob(uint salt) at_step(2) public payable {
        require(keccak256(salt) == bytes32(commitsBob[msg.sender]));
        if (chosenRoleBob != address(0x0))
             require(timesBob[msg.sender] < timesBob[chosenRoleBob]);
        role[msg.sender] = Role.Bob;
        balanceOf[msg.sender] = msg.value;
        chosenRoleBob = msg.sender;
        require(true);
    }
    event Broadcast2(); // TODO: add params
    function __nextStep2() at_step(2) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast2();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 2
    // step 3
    uint Issuer_hidden_c;
    bool Issuer_hidden_c_done;
    bool done_Issuer_3;
    function yield_Issuer3(uint _hidden_c) at_step(3) public {
        require(role[msg.sender] == Role.Issuer);
        require(!done_Issuer_3);
        require(true);
        Issuer_hidden_c = _hidden_c;
        Issuer_hidden_c_done = true;
        done_Issuer_3 = true;
    }
    uint Alice_hidden_c;
    bool Alice_hidden_c_done;
    bool done_Alice_3;
    function yield_Alice3(uint _hidden_c) at_step(3) public {
        require(role[msg.sender] == Role.Alice);
        require(!done_Alice_3);
        require(true);
        Alice_hidden_c = _hidden_c;
        Alice_hidden_c_done = true;
        done_Alice_3 = true;
    }
    uint Bob_hidden_c;
    bool Bob_hidden_c_done;
    bool done_Bob_3;
    function yield_Bob3(uint _hidden_c) at_step(3) public {
        require(role[msg.sender] == Role.Bob);
        require(!done_Bob_3);
        require(true);
        Bob_hidden_c = _hidden_c;
        Bob_hidden_c_done = true;
        done_Bob_3 = true;
    }
    event Broadcast3(); // TODO: add params
    function __nextStep3() at_step(3) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast3();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 3
    // step 4
    int Issuer_c;
    bool Issuer_c_done;
    bool done_Issuer_4;
    function reveal_Issuer4(int _c, uint salt) at_step(4) public {
        require(role[msg.sender] == Role.Issuer);
        require(!done_Issuer_4);
        require(keccak256(_c, salt) == bytes32(Issuer_hidden_c));
        require(true);
        Issuer_c = _c;
        Issuer_c_done = true;
        done_Issuer_4 = true;
    }
    int Alice_c;
    bool Alice_c_done;
    bool done_Alice_4;
    function reveal_Alice4(int _c, uint salt) at_step(4) public {
        require(role[msg.sender] == Role.Alice);
        require(!done_Alice_4);
        require(keccak256(_c, salt) == bytes32(Alice_hidden_c));
        require(true);
        Alice_c = _c;
        Alice_c_done = true;
        done_Alice_4 = true;
    }
    int Bob_c;
    bool Bob_c_done;
    bool done_Bob_4;
    function reveal_Bob4(int _c, uint salt) at_step(4) public {
        require(role[msg.sender] == Role.Bob);
        require(!done_Bob_4);
        require(keccak256(_c, salt) == bytes32(Bob_hidden_c));
        require(true);
        Bob_c = _c;
        Bob_c_done = true;
        done_Bob_4 = true;
    }
    event Broadcast4(); // TODO: add params
    function __nextStep4() at_step(4) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast4();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 4
}
