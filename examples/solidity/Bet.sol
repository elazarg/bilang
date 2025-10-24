pragma solidity ^0.8.31;

contract Bet {
    constructor() {
        lastTs = block.timestamp;
    }

    enum Role { None, Gambler, Race }

    uint256 constant public PHASE_TIME = uint256(500);

    uint256 public phase;

    uint256 public lastTs;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Gambler;

    address public address_Race;

    bool public payoffs_distributed;

    bool public done_Race;

    bool public done_Phase0_Race;

    bool public done_Gambler;

    int256 public Gambler_bet;

    bool public done_Gambler_bet;

    bool public done_Phase1_Gambler;

    int256 public Race_winner;

    bool public done_Race_winner;

    bool public done_Phase2_Race;

    modifier at_phase(uint256 _phase) {
        require((phase == _phase), "wrong phase");
    }

    modifier by(Role r) {
        require((role[msg.sender] == r), "bad role");
    }

    modifier at_final_phase() {
        require((phase == 3), "game not over");
        require((!payoffs_distributed), "payoffs already sent");
    }

    function keccak(bool x, uint256 salt) public pure returns (bytes32 out) {
        return keccak256(abi.encodePacked(x, salt));
    }

    function join_Race() public payable by(Role.None) at_phase(0) {
        require((!done_Race), "already joined");
        role[msg.sender] = Role.Race;
        address_Race = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Race = true;
        done_Phase0_Race = true;
    }

    function __nextPhase_Phase0() public {
        require((phase == 0), "wrong phase");
        require(done_Phase0_Race, "Race not done");
        emit Broadcast_Phase0();
        phase = 1;
        lastTs = block.timestamp;
    }

    function join_Gambler(int256 _bet) public payable by(Role.None) at_phase(1) {
        require((!done_Gambler), "already joined");
        role[msg.sender] = Role.Gambler;
        address_Gambler = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Gambler = true;
        require((((_bet == 1) || (_bet == 2)) || (_bet == 3)), "domain");
        Gambler_bet = _bet;
        done_Gambler_bet = true;
        done_Phase1_Gambler = true;
    }

    function __nextPhase_Phase1() public {
        require((phase == 1), "wrong phase");
        require(done_Phase1_Gambler, "Gambler not done");
        emit Broadcast_Phase1();
        phase = 2;
        lastTs = block.timestamp;
    }

    function yield_Phase2_Race(int256 _winner) public by(Role.Race) at_phase(2) {
        require((!done_Phase2_Race), "done");
        require((((_winner == 1) || (_winner == 2)) || (_winner == 3)), "domain");
        Race_winner = _winner;
        done_Race_winner = true;
        done_Phase2_Race = true;
    }

    function __nextPhase_Phase2() public {
        require((phase == 2), "wrong phase");
        require(done_Phase2_Race, "Race not done");
        emit Broadcast_Phase2();
        phase = 3;
        lastTs = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_Gambler] = (((!done_Race_winner) || (Race_winner == Gambler_bet))) ? 100 : 0;
        balanceOf[address_Race] = (((!done_Race_winner) || (Race_winner == Gambler_bet))) ? 0 : 100;
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

    receive() public payable {
        revert("direct ETH not allowed");
    }
}
