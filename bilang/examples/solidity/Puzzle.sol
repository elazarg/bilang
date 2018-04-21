pragma solidity ^0.4.22;
contract Puzzle {
    // roles
    enum Role { None, Q, A }
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
    int Q_x;
    bool Q_x_done;
    bool done_Q_0;
    function join_Q(int _x) at_step(0) public payable {
        require(role[msg.sender] == Role.None);
        require(!done_Q_0);
        role[msg.sender] = Role.Q;
        balanceOf[msg.sender] = msg.value;
        require(true);
        Q_x = _x;
        Q_x_done = true;
        done_Q_0 = true;
    }
    event Broadcast0(); // TODO: add params
    function __nextStep0() at_step(0) public {
        emit Broadcast0();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 0
    // step 1
    int A_p;
    int A_q;
    bool A_p_done;
    bool A_q_done;
    bool done_A_1;
    function join_A(int _p, int _q) at_step(1) public payable {
        require(role[msg.sender] == Role.None);
        require(!done_A_1);
        role[msg.sender] = Role.A;
        balanceOf[msg.sender] = msg.value;
        require(((p * q) == x));
        A_p = _p;
    A_q = _q;
        A_p_done = true;
    A_q_done = true;
        done_A_1 = true;
    }
    event Broadcast1(); // TODO: add params
    function __nextStep1() at_step(1) public {
        emit Broadcast1();
        step += 1;
        __lastStep = block.timestamp;
    }
    // end 1
}
