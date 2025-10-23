pragma solidity ^0.8.31;

contract TicTacToe {
    constructor() {
            lastTs = block.timestamp;
    }

    enum Role { None, X, O }

    uint256 constant public PHASE_TIME = uint256(500);

    uint256 public phase;

    uint256 public lastTs;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_X;

    address public address_O;

    bool public payoffs_distributed;

    bool public done_X;

    bool public done_Phase0_X;

    bool public done_O;

    bool public done_Phase1_O;

    int256 public X_c1;

    bool public done_X_c1;

    bool public done_Phase2_X;

    int256 public O_c1;

    bool public done_O_c1;

    bool public done_Phase3_O;

    int256 public X_c2;

    bool public done_X_c2;

    bool public done_Phase4_X;

    int256 public O_c2;

    bool public done_O_c2;

    bool public done_Phase5_O;

    int256 public X_c3;

    bool public done_X_c3;

    bool public done_Phase6_X;

    int256 public O_c3;

    bool public done_O_c3;

    bool public done_Phase7_O;

    int256 public X_c4;

    bool public done_X_c4;

    bool public done_Phase8_X;

    int256 public O_c4;

    bool public done_O_c4;

    bool public done_Phase9_O;

    modifier at_phase(uint256 _phase) {
            require((phase == _phase), "wrong phase");
    }

    modifier by(Role r) {
            require((role[msg.sender] == r), "bad role");
    }

    modifier at_final_phase() {
            require((phase == 10), "game not over");
            require((!payoffs_distributed), "payoffs already sent");
    }

    function keccak(bool x, uint256 salt) public pure returns (bytes32 out) {
            return keccak256(abi.encodePacked(x, salt));
    }

    function join_X() public payable by(Role.None) at_phase(0) {
            require((!done_X), "already joined");
            role[msg.sender] = Role.X;
            address_X = msg.sender;
            require((msg.value == 100), "bad stake");
            balanceOf[msg.sender] = msg.value;
            done_X = true;
            done_Phase0_X = true;
    }

    function __nextPhase_Phase0() public {
            require((phase == 0), "wrong phase");
            require(done_Phase0_X, "X not done");
            emit Broadcast_Phase0();
            phase = 1;
            lastTs = block.timestamp;
    }

    function join_O() public payable by(Role.None) at_phase(1) {
            require((!done_O), "already joined");
            role[msg.sender] = Role.O;
            address_O = msg.sender;
            require((msg.value == 100), "bad stake");
            balanceOf[msg.sender] = msg.value;
            done_O = true;
            done_Phase1_O = true;
    }

    function __nextPhase_Phase1() public {
            require((phase == 1), "wrong phase");
            require(done_Phase1_O, "O not done");
            emit Broadcast_Phase1();
            phase = 2;
            lastTs = block.timestamp;
    }

    function yield_Phase2_X(int256 _c1) public by(Role.X) at_phase(2) {
            require((!done_Phase2_X), "done");
            require((((_c1 == 0) || (_c1 == 1)) || (_c1 == 4)), "domain");
            X_c1 = _c1;
            done_X_c1 = true;
            done_Phase2_X = true;
    }

    function __nextPhase_Phase2() public {
            require((phase == 2), "wrong phase");
            require(done_Phase2_X, "X not done");
            emit Broadcast_Phase2();
            phase = 3;
            lastTs = block.timestamp;
    }

    function yield_Phase3_O(int256 _c1) public by(Role.O) at_phase(3) {
            require((!done_Phase3_O), "done");
            require((((((_c1 == 1) || (_c1 == 3)) || (_c1 == 4)) || (_c1 == 5)) || (_c1 == 9)), "domain");
            require((_c1 != _c1), "where");
            O_c1 = _c1;
            done_O_c1 = true;
            done_Phase3_O = true;
    }

    function __nextPhase_Phase3() public {
            require((phase == 3), "wrong phase");
            require(done_Phase3_O, "O not done");
            emit Broadcast_Phase3();
            phase = 4;
            lastTs = block.timestamp;
    }

    function yield_Phase4_X(int256 _c2) public by(Role.X) at_phase(4) {
            require((!done_Phase4_X), "done");
            require((((((((((_c2 == 0) || (_c2 == 1)) || (_c2 == 2)) || (_c2 == 3)) || (_c2 == 4)) || (_c2 == 5)) || (_c2 == 6)) || (_c2 == 7)) || (_c2 == 8)), "domain");
            require((((X_c1 != O_c1) && (X_c1 != _c2)) && (O_c1 != _c2)), "where");
            X_c2 = _c2;
            done_X_c2 = true;
            done_Phase4_X = true;
    }

    function __nextPhase_Phase4() public {
            require((phase == 4), "wrong phase");
            require(done_Phase4_X, "X not done");
            emit Broadcast_Phase4();
            phase = 5;
            lastTs = block.timestamp;
    }

    function yield_Phase5_O(int256 _c2) public by(Role.O) at_phase(5) {
            require((!done_Phase5_O), "done");
            require((((((((((_c2 == 0) || (_c2 == 1)) || (_c2 == 2)) || (_c2 == 3)) || (_c2 == 4)) || (_c2 == 5)) || (_c2 == 6)) || (_c2 == 7)) || (_c2 == 8)), "domain");
            require(((((((X_c1 != O_c1) && (X_c1 != _c2)) && (X_c1 != _c2)) && (O_c1 != _c2)) && (O_c1 != _c2)) && (_c2 != _c2)), "where");
            O_c2 = _c2;
            done_O_c2 = true;
            done_Phase5_O = true;
    }

    function __nextPhase_Phase5() public {
            require((phase == 5), "wrong phase");
            require(done_Phase5_O, "O not done");
            emit Broadcast_Phase5();
            phase = 6;
            lastTs = block.timestamp;
    }

    function yield_Phase6_X(int256 _c3) public by(Role.X) at_phase(6) {
            require((!done_Phase6_X), "done");
            require((((((((((_c3 == 0) || (_c3 == 1)) || (_c3 == 2)) || (_c3 == 3)) || (_c3 == 4)) || (_c3 == 5)) || (_c3 == 6)) || (_c3 == 7)) || (_c3 == 8)), "domain");
            require(((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != _c3)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != _c3)) && (X_c2 != O_c2)) && (X_c2 != _c3)) && (O_c2 != _c3)), "where");
            X_c3 = _c3;
            done_X_c3 = true;
            done_Phase6_X = true;
    }

    function __nextPhase_Phase6() public {
            require((phase == 6), "wrong phase");
            require(done_Phase6_X, "X not done");
            emit Broadcast_Phase6();
            phase = 7;
            lastTs = block.timestamp;
    }

    function yield_Phase7_O(int256 _c3) public by(Role.O) at_phase(7) {
            require((!done_Phase7_O), "done");
            require((((((((((_c3 == 0) || (_c3 == 1)) || (_c3 == 2)) || (_c3 == 3)) || (_c3 == 4)) || (_c3 == 5)) || (_c3 == 6)) || (_c3 == 7)) || (_c3 == 8)), "domain");
            require((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != _c3)) && (X_c1 != _c3)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != _c3)) && (O_c1 != _c3)) && (X_c2 != O_c2)) && (X_c2 != _c3)) && (X_c2 != _c3)) && (O_c2 != _c3)) && (O_c2 != _c3)) && (_c3 != _c3)), "where");
            O_c3 = _c3;
            done_O_c3 = true;
            done_Phase7_O = true;
    }

    function __nextPhase_Phase7() public {
            require((phase == 7), "wrong phase");
            require(done_Phase7_O, "O not done");
            emit Broadcast_Phase7();
            phase = 8;
            lastTs = block.timestamp;
    }

    function yield_Phase8_X(int256 _c4) public by(Role.X) at_phase(8) {
            require((!done_Phase8_X), "done");
            require((((((((((_c4 == 0) || (_c4 == 1)) || (_c4 == 2)) || (_c4 == 3)) || (_c4 == 4)) || (_c4 == 5)) || (_c4 == 6)) || (_c4 == 7)) || (_c4 == 8)), "domain");
            require((((((((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != O_c3)) && (X_c1 != _c4)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != O_c3)) && (O_c1 != _c4)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != O_c3)) && (X_c2 != _c4)) && (O_c2 != X_c3)) && (O_c2 != O_c3)) && (O_c2 != _c4)) && (X_c3 != O_c3)) && (X_c3 != _c4)) && (O_c3 != _c4)), "where");
            X_c4 = _c4;
            done_X_c4 = true;
            done_Phase8_X = true;
    }

    function __nextPhase_Phase8() public {
            require((phase == 8), "wrong phase");
            require(done_Phase8_X, "X not done");
            emit Broadcast_Phase8();
            phase = 9;
            lastTs = block.timestamp;
    }

    function yield_Phase9_O(int256 _c4) public by(Role.O) at_phase(9) {
            require((!done_Phase9_O), "done");
            require((((((((((_c4 == 0) || (_c4 == 1)) || (_c4 == 2)) || (_c4 == 3)) || (_c4 == 4)) || (_c4 == 5)) || (_c4 == 6)) || (_c4 == 7)) || (_c4 == 8)), "domain");
            require(((((((((((((((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != O_c3)) && (X_c1 != _c4)) && (X_c1 != _c4)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != O_c3)) && (O_c1 != _c4)) && (O_c1 != _c4)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != O_c3)) && (X_c2 != _c4)) && (X_c2 != _c4)) && (O_c2 != X_c3)) && (O_c2 != O_c3)) && (O_c2 != _c4)) && (O_c2 != _c4)) && (X_c3 != O_c3)) && (X_c3 != _c4)) && (X_c3 != _c4)) && (O_c3 != _c4)) && (O_c3 != _c4)) && (_c4 != _c4)), "where");
            O_c4 = _c4;
            done_O_c4 = true;
            done_Phase9_O = true;
    }

    function __nextPhase_Phase9() public {
            require((phase == 9), "wrong phase");
            require(done_Phase9_O, "O not done");
            emit Broadcast_Phase9();
            phase = 10;
            lastTs = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
            payoffs_distributed = true;
            balanceOf[address_X] = 0;
            balanceOf[address_O] = 0;
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

    event Broadcast_Phase5();

    event Broadcast_Phase6();

    event Broadcast_Phase7();

    event Broadcast_Phase8();

    event Broadcast_Phase9();

    receive() public payable {
            revert("direct ETH not allowed");
    }
}