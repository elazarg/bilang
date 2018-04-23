pragma solidity ^0.4.22;
contract ThreeWayLotteryShort {
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
    int Issuer_c;
    bool Issuer_c_done;
    function join_Issuer(int _c, uint salt) at_step(0) public payable {
        require(keccak256(_c, salt) == bytes32(commitsIssuer[msg.sender]));
        if (chosenRoleIssuer != address(0x0))
             require(timesIssuer[msg.sender] < timesIssuer[chosenRoleIssuer]);
        role[msg.sender] = Role.Issuer;
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
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepAlice == false);
        emit BroadcastHalfAlice();
        halfStepAlice = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleAlice;
    int Alice_c;
    bool Alice_c_done;
    function join_Alice(int _c, uint salt) at_step(0) public payable {
        require(keccak256(_c, salt) == bytes32(commitsAlice[msg.sender]));
        if (chosenRoleAlice != address(0x0))
             require(timesAlice[msg.sender] < timesAlice[chosenRoleAlice]);
        role[msg.sender] = Role.Alice;
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
        require(block.timestamp >= __lastStep + STEP_TIME);
        require(halfStepBob == false);
        emit BroadcastHalfBob();
        halfStepBob = true;
        __lastStep = block.timestamp;
    }
    address chosenRoleBob;
    int Bob_c;
    bool Bob_c_done;
    function join_Bob(int _c, uint salt) at_step(0) public payable {
        require(keccak256(_c, salt) == bytes32(commitsBob[msg.sender]));
        if (chosenRoleBob != address(0x0))
             require(timesBob[msg.sender] < timesBob[chosenRoleBob]);
        role[msg.sender] = Role.Bob;
        balanceOf[msg.sender] = msg.value;
        chosenRoleBob = msg.sender;
        require(true);
        Bob_c = _c;
        Bob_c_done = true;
    }
    event Broadcast0(); // TODO: add params
    function __nextStep0() at_step(0) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast0();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 0
    function withdraw_1_Bob() by(Role.Bob) public at_step(1) {
        require(role[msg.sender] == Role.Bob);
        // uint amount = balanceOf[msg.sender];
        uint amount;
        bool freshVar83;
        {
        bool freshVar84;
        freshVar84 = Alice_c_done;
        bool freshVar85;
        freshVar85 = Bob_c_done;
        freshVar83 = freshVar84 || freshVar85;
        }
        if (freshVar83) { 
        amount = (- 10);
        } else {
        bool freshVar86;
        freshVar86 = Issuer_c_done;
        if (freshVar86) { 
        amount = (- 10);
        } else {
        amount = (((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == ((Issuer_c + Alice_c) + Bob_c))) ? (- 10) : (((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == (((Issuer_c + Alice_c) + Bob_c) - 1))) ? 20 : (- 10)));
        }
        }
        // balanceOf[msg.sender] = 0;
        msg.sender.transfer(amount);
    }
    function withdraw_1_Issuer() by(Role.Issuer) public at_step(1) {
        require(role[msg.sender] == Role.Issuer);
        // uint amount = balanceOf[msg.sender];
        uint amount;
        bool freshVar87;
        {
        bool freshVar88;
        freshVar88 = Alice_c_done;
        bool freshVar89;
        freshVar89 = Bob_c_done;
        freshVar87 = freshVar88 || freshVar89;
        }
        if (freshVar87) { 
        amount = 20;
        } else {
        bool freshVar90;
        freshVar90 = Issuer_c_done;
        if (freshVar90) { 
        amount = (- 10);
        } else {
        amount = (((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == ((Issuer_c + Alice_c) + Bob_c))) ? (- 10) : (((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == (((Issuer_c + Alice_c) + Bob_c) - 1))) ? (- 10) : 20));
        }
        }
        // balanceOf[msg.sender] = 0;
        msg.sender.transfer(amount);
    }
    function withdraw_1_Alice() by(Role.Alice) public at_step(1) {
        require(role[msg.sender] == Role.Alice);
        // uint amount = balanceOf[msg.sender];
        uint amount;
        bool freshVar91;
        {
        bool freshVar92;
        freshVar92 = Alice_c_done;
        bool freshVar93;
        freshVar93 = Bob_c_done;
        freshVar91 = freshVar92 || freshVar93;
        }
        if (freshVar91) { 
        amount = (- 10);
        } else {
        bool freshVar94;
        freshVar94 = Issuer_c_done;
        if (freshVar94) { 
        amount = 20;
        } else {
        amount = (((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == ((Issuer_c + Alice_c) + Bob_c))) ? 20 : (((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == (((Issuer_c + Alice_c) + Bob_c) - 1))) ? (- 10) : (- 10)));
        }
        }
        // balanceOf[msg.sender] = 0;
        msg.sender.transfer(amount);
    }
}
