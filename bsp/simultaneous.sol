pragma solidity ^0.4.17;
library P {
    uint constant EVEN = 0;
    uint constant ODD = 1;
}

contract Bsp {
    Session[] _sessions;
    address[] _clients;
    
    uint constant total = 2;
    
    uint _count;

    uint public step;
    mapping(address => uint) finished_step;

    event StartSession(Session);
    event NextStep();

    function Bsp() public {
        // first count is for joiners
        _count = total;
    }

    function join(uint client_num) public {
        // this is `done()` special cased - before we know the participants
        address client = msg.sender;
        require(_clients[client_num] == address(0x0));
        _clients[client_num] = client;
        Session s = new Session(client_num, client, this);
        _sessions[client_num] = s;
        StartSession(s);
        _count--;
    }

    function done(uint client_num) public {
        Session subserver = Session(msg.sender);
        require(subserver == _sessions[client_num]);
        require(finished_step[subserver] == step - 1);
        finished_step[subserver] = step;
        _count--;
        //updateGlobal(_evenState);
    }

    function next() public {
        require(_count == 0);
        _count = total;
        step++;
        NextStep();
    }
}

contract Session {
    uint _client_num;
    address _client;
    Bsp _server;

    bytes32 _step_1_h;
    bool _step_2_choice;

    function Session(uint client_num, address client, Bsp server) public { 
        _client = client;
        _server = server;
        _client_num = client_num;
    }

    function step_1(bytes32 h) public {
        require(_server.step() == 1);
        require(msg.sender == _client);

        _step_1_h = h;

        _server.done(_client_num);
    }

    function step_2(bool choice, uint256 salt) public {
        require(_server.step() == 2);
        require(msg.sender == _client);

        require(keccak256(choice, salt, msg.sender) == _step_1_h);
        delete _step_1_h;
        _step_2_choice = choice;

        _server.done(_client_num);
    }

    function step_3() {
        if (_server.win() == _client_num)
            Won();
        else
            Lost();
    }

    event Won();
    event Lost();
}
