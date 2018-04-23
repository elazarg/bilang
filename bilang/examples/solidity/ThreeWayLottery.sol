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
    int Issuer_c;
    bool Issuer_c_done;
    bool done_Issuer_3;
    function yield_Issuer3(int _c) at_step(3) public {
        require(role[msg.sender] == Role.Issuer);
        require(!done_Issuer_3);
        require(true);
        Issuer_c = _c;
        Issuer_c_done = true;
        done_Issuer_3 = true;
    }
    int Alice_c;
    bool Alice_c_done;
    bool done_Alice_3;
    function yield_Alice3(int _c) at_step(3) public {
        require(role[msg.sender] == Role.Alice);
        require(!done_Alice_3);
        require(true);
        Alice_c = _c;
        Alice_c_done = true;
        done_Alice_3 = true;
    }
    int Bob_c;
    bool Bob_c_done;
    bool done_Bob_3;
    function yield_Bob3(int _c) at_step(3) public {
        require(role[msg.sender] == Role.Bob);
        require(!done_Bob_3);
        require(true);
        Bob_c = _c;
        Bob_c_done = true;
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
    function withdraw_4_Bob() by(Role.Bob) public at_step(4) {
        require(role[msg.sender] == Role.Bob);
        int amount;
        bool freshVar71;
        {
        bool freshVar72;
        freshVar72 = Alice_c_done;
        bool freshVar73;
        freshVar73 = Bob_c_done;
        freshVar71 = freshVar72 || freshVar73;
        }
        if (freshVar71) { 
        amount = (- int(10));
        } else {
        bool freshVar74;
        freshVar74 = Issuer_c_done;
        if (freshVar74) { 
        amount = (- int(10));
        } else {
        amount = (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == ((Issuer_c + Alice_c) + Bob_c))) ? (- int(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == (((Issuer_c + Alice_c) + Bob_c) - int(1)))) ? int(20) : (- int(10))));
        }
        }
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_4_Issuer() by(Role.Issuer) public at_step(4) {
        require(role[msg.sender] == Role.Issuer);
        int amount;
        bool freshVar75;
        {
        bool freshVar76;
        freshVar76 = Alice_c_done;
        bool freshVar77;
        freshVar77 = Bob_c_done;
        freshVar75 = freshVar76 || freshVar77;
        }
        if (freshVar75) { 
        amount = int(20);
        } else {
        bool freshVar78;
        freshVar78 = Issuer_c_done;
        if (freshVar78) { 
        amount = (- int(10));
        } else {
        amount = (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == ((Issuer_c + Alice_c) + Bob_c))) ? (- int(10)) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == (((Issuer_c + Alice_c) + Bob_c) - int(1)))) ? (- int(10)) : int(20)));
        }
        }
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_4_Alice() by(Role.Alice) public at_step(4) {
        require(role[msg.sender] == Role.Alice);
        int amount;
        bool freshVar79;
        {
        bool freshVar80;
        freshVar80 = Alice_c_done;
        bool freshVar81;
        freshVar81 = Bob_c_done;
        freshVar79 = freshVar80 || freshVar81;
        }
        if (freshVar79) { 
        amount = (- int(10));
        } else {
        bool freshVar82;
        freshVar82 = Issuer_c_done;
        if (freshVar82) { 
        amount = int(20);
        } else {
        amount = (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == ((Issuer_c + Alice_c) + Bob_c))) ? int(20) : (((((((Issuer_c + Alice_c) + Bob_c) / int(3)) * int(3)) == (((Issuer_c + Alice_c) + Bob_c) - int(1)))) ? (- int(10)) : (- int(10))));
        }
        }
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
