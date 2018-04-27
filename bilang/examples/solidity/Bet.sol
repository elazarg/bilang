pragma solidity ^0.4.22;
contract Bet {
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
    enum Role { None, Gambler }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;
    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
    // step 0
    bool doneRace;
    function join_Race() at_step(0) public by(Role.None) payable {
        require(!doneRace);
        role[msg.sender] = Role.Race;
        require(msg.value == 100); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        doneRace = true;
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
    // step 1
    mapping(address => bytes32) commitsGambler;
    mapping(address => uint) timesGambler;
    bool halfStepGambler;
    function join_commit_Gambler(bytes32 c) at_step(1) public {
        require(commitsGambler[msg.sender] == bytes32(0));
        require(!halfStepGambler);
        commitsGambler[msg.sender] = c;
        timesGambler[msg.sender] = block.timestamp;
    }
    event BroadcastHalfGambler();
    function __nextHalfStepGambler() at_step(1) public {
        require(block.timestamp >= lastBlock + STEP_TIME);
        require(halfStepGambler == false);
        emit BroadcastHalfGambler();
        halfStepGambler = true;
        lastBlock = block.timestamp;
    }
    int Gambler_bet;
    bool Gambler_bet_done;
    function join_Gambler(int _bet, uint salt) at_step(1) public payable {
        require(keccak256(_bet, salt) == bytes32(commitsGambler[msg.sender]));
        role[msg.sender] = Role.Gambler;
        require(msg.value == 100); 
        balanceOf[msg.sender] = msg.value;
        require(true);
        Gambler_bet = _bet;
        Gambler_bet_done = true;
    }
    event Broadcast1(); // TODO: add params
    function __nextStep1() public {
        require(step == 1);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast1();
        step = 2;
        lastBlock = block.timestamp;
    }
    // end 1
    // step 2
    int Race_winner;
    bool Race_winner_done;
    bool done_Race_2;
    function yield_Race2(int _winner) by (Role.Race) at_step(2) public {
        require(!done_Race_2);
        require(true);
        Race_winner = _winner;
        Race_winner_done = true;
        done_Race_2 = true;
    }
    event Broadcast2(); // TODO: add params
    function __nextStep2() public {
        require(step == 2);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast2();
        step = 3;
        lastBlock = block.timestamp;
    }
    // end 2
    function withdraw_3_Gambler() by(Role.Gambler) at_step(3) public {
        int amount = (((! Race_winner_done || (Race_winner == Gambler_bet))) ? int(100) : int(0));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
    function withdraw_3_Race() by(Role.Race) at_step(3) public {
        int amount = (((! Race_winner_done || (Race_winner == Gambler_bet))) ? int(0) : int(100));
        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        delete balanceOf[msg.sender];
    }
}
