pragma solidity ^0.8.31;

contract Simple {
    constructor() {
        lastTs = block.timestamp;
    }

    enum Role { None, A, B }

    uint256 constant public PHASE_TIME = uint256(500);

    uint256 public phase;

    uint256 public lastTs;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_A;

    address public address_B;

    bool public payoffs_distributed;

    bool public done_A;

    bool public done_Phase0_A;

    bool public done_B;

    bool public done_Phase1_B;

    uint256 public A_hidden_c;

    bool public done_A_hidden_c;

    bool public A_c;

    bool public done_A_c;

    bool public done_Phase2_A;

    bool public B_c;

    bool public done_B_c;

    bool public done_Phase3_B;

    bool public done_Phase4_A;

    modifier at_phase(uint256 _phase) {
        require((phase == _phase), "wrong phase");
    }

    modifier by(Role r) {
        require((role[msg.sender] == r), "bad role");
    }

    modifier at_final_phase() {
        require((phase == 5), "game not over");
        require((!payoffs_distributed), "payoffs already sent");
    }

    function keccak(bool x, uint256 salt) public pure returns (bytes32 out) {
        return keccak256(abi.encodePacked(x, salt));
    }

    function join_A() public payable by(Role.None) at_phase(0) {
        require((!done_A), "already joined");
        role[msg.sender] = Role.A;
        address_A = msg.sender;
        require((msg.value == 1), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_A = true;
        done_Phase0_A = true;
    }

    function __nextPhase_Phase0() public {
        require((phase == 0), "wrong phase");
        require(done_Phase0_A, "A not done");
        emit Broadcast_Phase0();
        phase = 1;
        lastTs = block.timestamp;
    }

    function join_B() public payable by(Role.None) at_phase(1) {
        require((!done_B), "already joined");
        role[msg.sender] = Role.B;
        address_B = msg.sender;
        require((msg.value == 1), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_B = true;
        done_Phase1_B = true;
    }

    function __nextPhase_Phase1() public {
        require((phase == 1), "wrong phase");
        require(done_Phase1_B, "B not done");
        emit Broadcast_Phase1();
        phase = 2;
        lastTs = block.timestamp;
    }

    function yield_Phase2_A(uint256 _hidden_c) public by(Role.A) at_phase(2) {
        require((!done_Phase2_A), "done");
        A_hidden_c = _hidden_c;
        done_A_hidden_c = true;
        done_Phase2_A = true;
    }

    function __nextPhase_Phase2() public {
        require((phase == 2), "wrong phase");
        require(done_Phase2_A, "A not done");
        emit Broadcast_Phase2();
        phase = 3;
        lastTs = block.timestamp;
    }

    function yield_Phase3_B(bool _c) public by(Role.B) at_phase(3) {
        require((!done_Phase3_B), "done");
        B_c = _c;
        done_B_c = true;
        done_Phase3_B = true;
    }

    function __nextPhase_Phase3() public {
        require((phase == 3), "wrong phase");
        require(done_Phase3_B, "B not done");
        emit Broadcast_Phase3();
        phase = 4;
        lastTs = block.timestamp;
    }

    function reveal_Phase4_A(bool _c, uint256 salt) public by(Role.A) at_phase(4) {
        require((!done_Phase4_A), "done");
        require((keccak256(abi.encodePacked(_c, salt)) == bytes32(A_hidden_c)), "bad reveal");
        A_c = _c;
        done_A_c = true;
        done_Phase4_A = true;
    }

    function __nextPhase_Phase4() public {
        require((phase == 4), "wrong phase");
        require(done_Phase4_A, "A not done");
        emit Broadcast_Phase4();
        phase = 5;
        lastTs = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_A] = (((A_c != B_c) || (!done_B_c))) ? 1 : (-1);
        balanceOf[address_B] = (((A_c == B_c) || (!done_A_c))) ? 1 : (-1);
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

    event Broadcast_Phase2();

    event Broadcast_Phase3();

    event Broadcast_Phase4();

    receive() public payable {
        revert("direct ETH not allowed");
    }
}