
pragma solidity ^0.4.22;
contract ThreeWayLottery {
    // roles
    enum Role { None, Issuer, Alice, Bob }
    mapping(address => Role) role;
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
        require(block.timestamp == __lastStep + STEP_TIME);
        _;
        __lastStep = block.timestamp;
    }
    // step 0
    function join_Issuer() at_step(0) public {
        require(role[msg.sender] == Role.None);
        role[msg.sender] = Role.Issuer;
        require(true);
    }
    event Broadcast0(); // TODO: add params
    function __nextStep0() public {
        emit Broadcast0();
    }
    // end 0
    // step 1
    function join_Alice() at_step(1) public {
        require(role[msg.sender] == Role.None);
        role[msg.sender] = Role.Alice;
        require(true);
    }
    event Broadcast1(); // TODO: add params
    function __nextStep1() public {
        emit Broadcast1();
    }
    // end 1
    // step 2
    function join_Bob() at_step(2) public {
        require(role[msg.sender] == Role.None);
        role[msg.sender] = Role.Bob;
        require(true);
    }
    event Broadcast2(); // TODO: add params
    function __nextStep2() public {
        emit Broadcast2();
    }
    // end 2
    // step 3
    uint Issuer_hidden_c;
    bool Issuer_hidden_c_done;
    function yield_Issuer3(uint _hidden_c) at_step(3) public {
        require(role[msg.sender] == Role.Issuer);
        require(true);
        Issuer_hidden_c = _hidden_c;
        Issuer_hidden_c_done = true;
    }
    uint Alice_hidden_c;
    bool Alice_hidden_c_done;
    function yield_Alice3(uint _hidden_c) at_step(3) public {
        require(role[msg.sender] == Role.Alice);
        require(true);
        Alice_hidden_c = _hidden_c;
        Alice_hidden_c_done = true;
    }
    uint Bob_hidden_c;
    bool Bob_hidden_c_done;
    function yield_Bob3(uint _hidden_c) at_step(3) public {
        require(role[msg.sender] == Role.Bob);
        require(true);
        Bob_hidden_c = _hidden_c;
        Bob_hidden_c_done = true;
    }
    event Broadcast3(); // TODO: add params
    function __nextStep3() public {
        emit Broadcast3();
    }
    // end 3
    // step 4
    int Issuer_c;
    bool Issuer_c_done;
    function reveal_Issuer4(int _c, uint salt) at_step(4) public {
        require(role[msg.sender] == Role.Issuer);
        require(keccak256(_c, salt) == bytes32(Issuer_hidden_c));
        require(true);
        Issuer_c = _c;
        Issuer_c_done = true;
    }
    int Alice_c;
    bool Alice_c_done;
    function reveal_Alice4(int _c, uint salt) at_step(4) public {
        require(role[msg.sender] == Role.Alice);
        require(keccak256(_c, salt) == bytes32(Alice_hidden_c));
        require(true);
        Alice_c = _c;
        Alice_c_done = true;
    }
    int Bob_c;
    bool Bob_c_done;
    function reveal_Bob4(int _c, uint salt) at_step(4) public {
        require(role[msg.sender] == Role.Bob);
        require(keccak256(_c, salt) == bytes32(Bob_hidden_c));
        require(true);
        Bob_c = _c;
        Bob_c_done = true;
    }
    event Broadcast4(); // TODO: add params
    function __nextStep4() public {
        emit Broadcast4();
    }
    // end 4
}
