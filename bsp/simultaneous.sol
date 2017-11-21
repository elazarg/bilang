pragma solidity ^0.4.17;

contract Bsp {
    Session[] _sessions;
    address[] _clients;
    
    uint constant total = 2;
    
    uint _count = total;

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
        require(client_num < total);
        require(_clients[client_num] == address(0x0));

        _clients[client_num] = client;

        Session s = new Session(client_num, client, this);
        _sessions[client_num] = s;
        StartSession(s);
        
        _count--;
    }

    function done_generic(uint client_num) internal {
        Session subserver = Session(msg.sender);
        require(subserver == _sessions[client_num]);
        require(finished_step[subserver] == step - 1);

        finished_step[subserver] = step;
        _count--;
        NextStep();
    }

    bool _choice_total = false;
    uint public win;

    // game-specific reduce
    function done_0(bytes32, uint client_num) public {
        done_generic(client_num);
    }

    function done_1(bool choice, uint client_num) public {
        done_generic(client_num);
        _choice_total = (_choice_total != choice);
    } 

    // next_* are called externally, by anybody
    function next_1() public { next_generic(); }

    function next_2() public {
        next_generic();
        win =  _choice_total ? 0 : 1; 
    }

    function next_generic() internal {
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

        _server.done_0(h, _client_num);
    }

    function step_2(bool choice, uint256 salt) public {
        require(_server.step() == 2);
        require(msg.sender == _client);

        require(keccak256(choice, salt, msg.sender) == _step_1_h);
        delete _step_1_h;
        _step_2_choice = choice;

        _server.done_1(choice, _client_num);
    }

    function step_3() public view returns(string) {
        if (_server.win() == _client_num)
            return "won";
        else
            return "lost";
    }
}


/**
Client code:

creator: a = create Bsp()

player1:

up = a.join(0)

() = await a.Next

salt = random()
choice = input()
h = hash(choice, me, salt)
up.step_1(h)

() = await a.Next

up.step_2(choice, salt)

() = await a.Next

result = step_3()
print(result)

*/