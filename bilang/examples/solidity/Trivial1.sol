pragma solidity ^0.4.22;
contract Trivial1 {
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
    enum Role { None, A }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
    // step 0
    bool doneA;
    function join_A() at_step(0) public by(Role.None) {
        require(!doneA);
        role[msg.sender] = Role.A;
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
    function withdraw_1_A() by(Role.A) at_step(1) public {
        int amount = int(0)
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
