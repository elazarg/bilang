pragma solidity ^0.8.31;

contract OddsEvensShort {
    constructor() {
        lastTs = block.timestamp;
    }

    enum Role { None, Odd, Even }

    uint256 constant public PHASE_TIME = uint256(500);

    uint256 public phase;

    uint256 public lastTs;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Odd;

    address public address_Even;

    bool public payoffs_distributed;

    bool public done_Odd;

    bool public Odd_c;

    bool public done_Odd_c;

    bool public done_Phase0_Odd;

    bool public done_Even;

    bool public Even_c;

    bool public done_Even_c;

    bool public done_Phase0_Even;

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

    function join_Odd(bool _c) public payable by(Role.None) at_phase(0) {
        require((!done_Odd), "already joined");
        role[msg.sender] = Role.Odd;
        address_Odd = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Odd = true;
        Odd_c = _c;
        done_Odd_c = true;
        done_Phase0_Odd = true;
    }

    function join_Even(bool _c) public payable by(Role.None) at_phase(0) {
        require((!done_Even), "already joined");
        role[msg.sender] = Role.Even;
        address_Even = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Even = true;
        Even_c = _c;
        done_Even_c = true;
        done_Phase0_Even = true;
    }

    function __nextPhase_Phase0() public {
        require((phase == 0), "wrong phase");
        require(done_Phase0_Odd, "Odd not done");
        require(done_Phase0_Even, "Even not done");
        emit Broadcast_Phase0();
        phase = 1;
        lastTs = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_Odd] = ((done_Even_c && done_Odd_c)) ? ((Even_c == Odd_c)) ? (-10) : 10 : (((!done_Even_c) && done_Odd_c)) ? 10 : (-100);
        balanceOf[address_Even] = ((done_Even_c && done_Odd_c)) ? ((Even_c == Odd_c)) ? 10 : (-10) : (((!done_Even_c) && done_Odd_c)) ? (-100) : (-100);
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