pragma solidity ^0.4.17;

contract Bsp {    
    uint constant total = 2;
    Session_Host _session_host;
    Session_Guest _session_guest;

    address[2] _clients;
    
    uint _count;

    uint public step;
    mapping(address => uint) finished_step;

    event StartSession(Session_Host);
    event StartSession(Session_Guest);
    event NextStep();

    function Bsp() public {
        // first count is for joiners
        _count = total;
    }

    function join_host(uint client_num) public {
        // this is `done()` special cased - before we know the participants
        address client = msg.sender;
        if (client_num >= total) revert();
        if (_clients[client_num] != address(0x0)) revert();

        _clients[client_num] = client;

        Session_Host s = new Session_Host(client_num, client, this);
        _session_host = s;
        StartSession(s);
        
        _count--;
    }
    function join_guest(uint client_num) public {
        // this is `done()` special cased - before we know the participants
        address client = msg.sender;
        if (client_num >= total) revert();
        if (_clients[client_num] != address(0x0)) revert();

        _clients[client_num] = client;

        Session_Guest s = new Session_Guest(client_num, client, this);
        _session_guest = s;
        StartSession(s);
        
        _count--;
    }
    function done_generic(uint client_num) internal {
        Session subserver = Session(msg.sender);
        require(subserver == (client_num == 0 ? Session(_session_host) : _session_guest));
        require(finished_step[subserver] == step - 1);

        finished_step[subserver] = step;
        _count--;
    }

    // game-specific reduce

    // option types :(
    int _Door1; event Door1(int);
    int _Goat; event Goat(int);
    int _Door2; event Door2(int);
    int _Car;

    uint public win;
    uint constant HOST = 0;
    uint constant GUEST = 1;

    function done_step_1(bytes32, uint client_num) public {
        require(client_num == HOST);
        done_generic(HOST);
    }

    function done_step_2(int door1, uint client_num) public {
        require(client_num == GUEST);
        done_generic(GUEST);
        _Door1 = door1;
        // publish event here and not on next, to make it constant time
        Door1(_Door1);
    } 

    function done_step_3(int goat, uint client_num) public {
        require(client_num == HOST);
        done_generic(HOST);
        _Goat = goat;
        Goat(_Goat);
    } 

    function done_step_4(int door2, uint client_num) public {
        require(client_num == GUEST);
        done_generic(GUEST);
        _Door2 = door2;
        Door2(_Door2);
    } 

    function done_step_5(int car, uint client_num) public {
        require(client_num == HOST);
        done_generic(HOST);
        _Car = car;
    }

    // next_* are called externally, by anybody
    function next_1() public {
        require(_count == 0);
        next_generic(1);
    }
    function next_2() public {
        require(_count == 0);
        next_generic(1);
    }
    function next_3() public {
        require(_count == 0);
        next_generic(1);
    }
    function next_4() public {
        require(_count == 0);
        next_generic(1);
    }

    function next_5() public {
        require(_count == 0);
        next_generic(1);

        win = (_Goat == _Car || _Door2 == _Car) ? GUEST : HOST;
    }

    function next_generic(uint next_count) internal {
        require(_count == 0);
        _count = next_count;
        step++;
        reset_timer();
        NextStep();
    }

    /// timer
    uint _next_timeout;
    function reset_timer() internal {
        _next_timeout = now + 1 days;
    }
    function timeout() public view returns(bool) {
        return _next_timeout < now;
    }

}

contract Session {
}

contract Session_Host is Session {
    uint constant _client_num = 0;
    address _client;
    Bsp _server;

    bytes32 _step_1_h;
    int _step_3_goat;
    int _step_5_car;

    function Session_Host(uint client_num, address client, Bsp server) public { 
        _client = client;
        _server = server;
        assert(_client_num == client_num);
    }

    function step_1(bytes32 h) public {
        require(_server.step() == 1);
        require(msg.sender == _client);

        _step_1_h = h;

        _server.done_step_1(h, _client_num);
    }

    function step_3(int goat) public {
        require(_server.step() == 3);
        require(msg.sender == _client);

        _step_3_goat = goat;

        _server.done_step_3(goat, _client_num);
    }

    function step_5(int car, uint256 salt) public {
        require(_server.step() == 5);
        require(msg.sender == _client);

        require(keccak256(car, salt, msg.sender) == _step_1_h);
        delete _step_1_h;
        _step_5_car = car;

        _server.done_step_5(car, _client_num);
    }

    function step_6() public view returns(string) {
        require(_server.step() == 6);
        if (_server.win() == _client_num)
            return "won";
        else
            return "lost";
    }
}

contract Session_Guest is Session {
    uint constant _client_num = 0;
    address _client;
    Bsp _server;

    int _step_2_door1;
    int _step_4_door2;

    function Session_Guest(uint client_num, address client, Bsp server) public { 
        _client = client;
        _server = server;
        assert(client_num == client_num);
    }

    function step_2(int door1) public {
        require(_server.step() == 2);
        require(msg.sender == _client);

        _step_2_door1 = door1;

        _server.done_step_2(door1, _client_num);
    }

    function step_4(int door2) public {
        require(_server.step() == 4);
        require(msg.sender == _client);

        _step_4_door2 = door2;

        _server.done_step_2(door2, _client_num);
    }

    function step_6() public view returns(string) {
        require(_server.step() == 6);
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

choice = input_bool()
salt = random()
h = hash(choice, me, salt)
up.step_1(h)

() = await a.Next

up.step_2(choice, salt)

() = await a.Next

result = step_3()
print(result)

*/