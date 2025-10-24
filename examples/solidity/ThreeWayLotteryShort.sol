pragma solidity ^0.8.31;

contract ThreeWayLotteryShort {
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

    int256 public Issuer_c;

    bool public done_Issuer_c;

    bool public done_Phase0_Issuer;

    bool public done_Alice;

    int256 public Alice_c;

    bool public done_Alice_c;

    bool public done_Phase0_Alice;

    bool public done_Bob;

    int256 public Bob_c;

    bool public done_Bob_c;

    bool public done_Phase0_Bob;

    modifier at_phase(uint256 _phase) {
        require((phase == _phase), "wrong phase");
    }

    modifier by(Role r) {
        require((role[msg.sender] == r), "bad role");
    }

    modifier at_final_phase() {
        require((phase == 1), "game not over");
        require((!payoffs_distributed), "payoffs already sent");
    }

    function keccak(bool x, uint256 salt) public pure returns (bytes32 out) {
        return keccak256(abi.encodePacked(x, salt));
    }

    function join_Issuer(int256 _c) public payable by(Role.None) at_phase(0) {
        require((!done_Issuer), "already joined");
        role[msg.sender] = Role.Issuer;
        address_Issuer = msg.sender;
        require((msg.value == 10), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Issuer = true;
        require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
        Issuer_c = _c;
        done_Issuer_c = true;
        done_Phase0_Issuer = true;
    }

    function join_Alice(int256 _c) public payable by(Role.None) at_phase(0) {
        require((!done_Alice), "already joined");
        role[msg.sender] = Role.Alice;
        address_Alice = msg.sender;
        require((msg.value == 10), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Alice = true;
        require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
        Alice_c = _c;
        done_Alice_c = true;
        done_Phase0_Alice = true;
    }

    function join_Bob(int256 _c) public payable by(Role.None) at_phase(0) {
        require((!done_Bob), "already joined");
        role[msg.sender] = Role.Bob;
        address_Bob = msg.sender;
        require((msg.value == 10), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Bob = true;
        require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
        Bob_c = _c;
        done_Bob_c = true;
        done_Phase0_Bob = true;
    }

    function __nextPhase_Phase0() public {
        require((phase == 0), "wrong phase");
        require(done_Phase0_Issuer, "Issuer not done");
        require(done_Phase0_Alice, "Alice not done");
        require(done_Phase0_Bob, "Bob not done");
        emit Broadcast_Phase0();
        phase = 1;
        lastTs = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_Issuer] = (((!done_Alice_c) || (!done_Bob_c))) ? 20 : ((!done_Issuer_c)) ? (-10) : ((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == ((Issuer_c + Alice_c) + Bob_c))) ? (-10) : ((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == (((Issuer_c + Alice_c) + Bob_c) - 1))) ? (-10) : 20;
        balanceOf[address_Alice] = (((!done_Alice_c) || (!done_Bob_c))) ? (-10) : ((!done_Issuer_c)) ? 20 : ((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == ((Issuer_c + Alice_c) + Bob_c))) ? 20 : ((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == (((Issuer_c + Alice_c) + Bob_c) - 1))) ? (-10) : (-10);
        balanceOf[address_Bob] = (((!done_Alice_c) || (!done_Bob_c))) ? (-10) : ((!done_Issuer_c)) ? (-10) : ((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == ((Issuer_c + Alice_c) + Bob_c))) ? (-10) : ((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == (((Issuer_c + Alice_c) + Bob_c) - 1))) ? 20 : (-10);
    }

    function withdraw() public {
        int256 bal = balanceOf[msg.sender];
        require((bal > 0), "no funds");
        balanceOf[msg.sender] = 0;
        (bool ok, ) = payable(msg.sender).call{value: uint256(bal)}("");
        require(ok, "ETH send failed");
    }

    event Broadcast_Phase0();

    receive() public payable {
        revert("direct ETH not allowed");
    }
}