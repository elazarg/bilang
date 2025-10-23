pragma solidity ^0.8.31;

contract Puzzle {
    constructor() {
            lastTs = block.timestamp;
    }

    enum Role { None, Q, A }

    uint256 constant public PHASE_TIME = uint256(500);

    uint256 public phase;

    uint256 public lastTs;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Q;

    address public address_A;

    bool public payoffs_distributed;

    bool public done_Q;

    int256 public Q_x;

    bool public done_Q_x;

    bool public done_Phase0_Q;

    bool public done_A;

    int256 public A_p;

    bool public done_A_p;

    int256 public A_q;

    bool public done_A_q;

    bool public done_Phase1_A;

    modifier at_phase(uint256 _phase) {
            require((phase == _phase), "wrong phase");
    }

    modifier by(Role r) {
            require((role[msg.sender] == r), "bad role");
    }

    modifier at_final_phase() {
            require((phase == 2), "game not over");
            require((!payoffs_distributed), "payoffs already sent");
    }

    function keccak(bool x, uint256 salt) public pure returns (bytes32 out) {
            return keccak256(abi.encodePacked(x, salt));
    }

    function join_Q(int256 _x) public payable by(Role.None) at_phase(0) {
            require((!done_Q), "already joined");
            role[msg.sender] = Role.Q;
            address_Q = msg.sender;
            require((msg.value == 50), "bad stake");
            balanceOf[msg.sender] = msg.value;
            done_Q = true;
            Q_x = _x;
            done_Q_x = true;
            done_Phase0_Q = true;
    }

    function __nextPhase_Phase0() public {
            require((phase == 0), "wrong phase");
            require(done_Phase0_Q, "Q not done");
            emit Broadcast_Phase0();
            phase = 1;
            lastTs = block.timestamp;
    }

    function join_A(int256 _p, int256 _q) public by(Role.None) at_phase(1) {
            require((!done_A), "already joined");
            role[msg.sender] = Role.A;
            address_A = msg.sender;
            done_A = true;
            require(((((_p * _q) == Q_x) && (_p != 1)) && (_q != 1)), "where");
            A_p = _p;
            done_A_p = true;
            A_q = _q;
            done_A_q = true;
            done_Phase1_A = true;
    }

    function __nextPhase_Phase1() public {
            require((phase == 1), "wrong phase");
            require(done_Phase1_A, "A not done");
            emit Broadcast_Phase1();
            phase = 2;
            lastTs = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
            payoffs_distributed = true;
            balanceOf[address_Q] = 0;
            balanceOf[address_A] = 50;
    }

    function withdraw() public {
            int256 bal = balanceOf[msg.sender];
            require((bal > 0), "no funds");
            balanceOf[msg.sender] = 0;
            (bool ok, ) = payable(msg.sender).call{value: uint256(bal)}("");
            require(ok, "ETH send failed");
    }

    event Broadcast_Phase0();

    event Broadcast_Phase1();

    receive() public payable {
            revert("direct ETH not allowed");
    }
}