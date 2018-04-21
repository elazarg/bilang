pragma solidity ^0.4.22;
contract OddsEvens {
    // roles
    enum Role { None, Odd, Even }
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
    bool done_Odd_0;
    function join_Odd() at_step(0) public payable {
        require(role[msg.sender] == Role.None);
        require(!done_Odd_0);
        role[msg.sender] = Role.Odd;
        balanceOf[msg.sender] = msg.value;
        require(true);
        done_Odd_0 = true;
    }
    bool done_Even_0;
    function join_Even() at_step(0) public payable {
        require(role[msg.sender] == Role.None);
        require(!done_Even_0);
        role[msg.sender] = Role.Even;
        balanceOf[msg.sender] = msg.value;
        require(true);
        done_Even_0 = true;
    }
    event Broadcast0(); // TODO: add params
    function __nextStep0() at_step(0) public {
        emit Broadcast0();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 0
    // step 1
    uint Odd_hidden_c;
    bool Odd_hidden_c_done;
    bool done_Odd_1;
    function yield_Odd1(uint _hidden_c) at_step(1) public {
        require(role[msg.sender] == Role.Odd);
        require(!done_Odd_1);
        require(true);
        Odd_hidden_c = _hidden_c;
        Odd_hidden_c_done = true;
        done_Odd_1 = true;
    }
    uint Even_hidden_c;
    bool Even_hidden_c_done;
    bool done_Even_1;
    function yield_Even1(uint _hidden_c) at_step(1) public {
        require(role[msg.sender] == Role.Even);
        require(!done_Even_1);
        require(true);
        Even_hidden_c = _hidden_c;
        Even_hidden_c_done = true;
        done_Even_1 = true;
    }
    event Broadcast1(); // TODO: add params
    function __nextStep1() at_step(1) public {
        emit Broadcast1();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 1
    // step 2
    bool Odd_c;
    bool Odd_c_done;
    bool done_Odd_2;
    function reveal_Odd2(bool _c, uint salt) at_step(2) public {
        require(role[msg.sender] == Role.Odd);
        require(!done_Odd_2);
        require(keccak256(_c, salt) == bytes32(Odd_hidden_c));
        require(true);
        Odd_c = _c;
        Odd_c_done = true;
        done_Odd_2 = true;
    }
    bool Even_c;
    bool Even_c_done;
    bool done_Even_2;
    function reveal_Even2(bool _c, uint salt) at_step(2) public {
        require(role[msg.sender] == Role.Even);
        require(!done_Even_2);
        require(keccak256(_c, salt) == bytes32(Even_hidden_c));
        require(true);
        Even_c = _c;
        Even_c_done = true;
        done_Even_2 = true;
    }
    event Broadcast2(); // TODO: add params
    function __nextStep2() at_step(2) public {
        emit Broadcast2();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 2
}
