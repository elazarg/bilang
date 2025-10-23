pragma solidity ^0.8.31;

contract ThreeWayLotteryBuggy {
    constructor() {
            lastTs = block.timestamp;
    }

    enum Role { None, Issuer, Alice, Bob }

    uint256 constant public PHASE_TIME = uint256(500);

    uint256 public phase;

    uint256 public lastTs;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Issuer;

    address public address_Alice;

    address public address_Bob;

    bool public payoffs_distributed;

    bool public done_Issuer;

    bool public done_Phase0_Issuer;

    bool public done_Alice;

    bool public done_Phase1_Alice;

    bool public done_Bob;

    bool public done_Phase2_Bob;

    int256 public Issuer_c;

    bool public done_Issuer_c;

    bool public done_Phase3_Issuer;

    int256 public Alice_c;

    bool public done_Alice_c;

    bool public done_Phase3_Alice;

    int256 public Bob_c;

    bool public done_Bob_c;

    bool public done_Phase3_Bob;

    modifier at_phase(uint256 _phase) {
            require((phase == _phase), "wrong phase");
    }

    modifier by(Role r) {
            require((role[msg.sender] == r), "bad role");
    }

    modifier at_final_phase() {
            require((phase == 4), "game not over");
            require((!payoffs_distributed), "payoffs already sent");
    }

    function keccak(bool x, uint256 salt) public pure returns (bytes32 out) {
            return keccak256(abi.encodePacked(x, salt));
    }

    function join_Issuer() public payable by(Role.None) at_phase(0) {
            require((!done_Issuer), "already joined");
            role[msg.sender] = Role.Issuer;
            address_Issuer = msg.sender;
            require((msg.value == 10), "bad stake");
            balanceOf[msg.sender] = msg.value;
            done_Issuer = true;
            done_Phase0_Issuer = true;
    }

    function __nextPhase_Phase0() public {
            require((phase == 0), "wrong phase");
            require(done_Phase0_Issuer, "Issuer not done");
            emit Broadcast_Phase0();
            phase = 1;
            lastTs = block.timestamp;
    }

    function join_Alice() public payable by(Role.None) at_phase(1) {
            require((!done_Alice), "already joined");
            role[msg.sender] = Role.Alice;
            address_Alice = msg.sender;
            require((msg.value == 10), "bad stake");
            balanceOf[msg.sender] = msg.value;
            done_Alice = true;
            done_Phase1_Alice = true;
    }

    function __nextPhase_Phase1() public {
            require((phase == 1), "wrong phase");
            require(done_Phase1_Alice, "Alice not done");
            emit Broadcast_Phase1();
            phase = 2;
            lastTs = block.timestamp;
    }

    function join_Bob() public payable by(Role.None) at_phase(2) {
            require((!done_Bob), "already joined");
            role[msg.sender] = Role.Bob;
            address_Bob = msg.sender;
            require((msg.value == 10), "bad stake");
            balanceOf[msg.sender] = msg.value;
            done_Bob = true;
            done_Phase2_Bob = true;
    }

    function __nextPhase_Phase2() public {
            require((phase == 2), "wrong phase");
            require(done_Phase2_Bob, "Bob not done");
            emit Broadcast_Phase2();
            phase = 3;
            lastTs = block.timestamp;
    }

    function yield_Phase3_Issuer(int256 _c) public by(Role.Issuer) at_phase(3) {
            require((!done_Phase3_Issuer), "done");
            require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
            Issuer_c = _c;
            done_Issuer_c = true;
            done_Phase3_Issuer = true;
    }

    function yield_Phase3_Alice(int256 _c) public by(Role.Alice) at_phase(3) {
            require((!done_Phase3_Alice), "done");
            require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
            Alice_c = _c;
            done_Alice_c = true;
            done_Phase3_Alice = true;
    }

    function yield_Phase3_Bob(int256 _c) public by(Role.Bob) at_phase(3) {
            require((!done_Phase3_Bob), "done");
            require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
            Bob_c = _c;
            done_Bob_c = true;
            done_Phase3_Bob = true;
    }

    function __nextPhase_Phase3() public {
            require((phase == 3), "wrong phase");
            require(done_Phase3_Issuer, "Issuer not done");
            require(done_Phase3_Alice, "Alice not done");
            require(done_Phase3_Bob, "Bob not done");
            emit Broadcast_Phase3();
            phase = 4;
            lastTs = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
            payoffs_distributed = true;
            balanceOf[address_Issuer] = (((!done_Alice_c) || (!done_Bob_c))) ? 20 : ((!done_Issuer_c)) ? (-10) : ((Alice_c == Bob_c)) ? 20 : ((((((Alice_c + Bob_c) + Issuer_c) / 2) * 2) == ((Alice_c + Bob_c) + Issuer_c))) ? (-10) : (-10);
            balanceOf[address_Alice] = (((!done_Alice_c) || (!done_Bob_c))) ? (-10) : ((!done_Issuer_c)) ? 20 : ((Alice_c == Bob_c)) ? (-10) : ((((((Alice_c + Bob_c) + Issuer_c) / 2) * 2) == ((Alice_c + Bob_c) + Issuer_c))) ? 20 : (-10);
            balanceOf[address_Bob] = (((!done_Alice_c) || (!done_Bob_c))) ? (-10) : ((!done_Issuer_c)) ? (-10) : ((Alice_c == Bob_c)) ? (-10) : ((((((Alice_c + Bob_c) + Issuer_c) / 2) * 2) == ((Alice_c + Bob_c) + Issuer_c))) ? (-10) : 20;
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

    receive() public payable {
            revert("direct ETH not allowed");
    }
}