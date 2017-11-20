pragma solidity ^0.4.17;

contract Bsp {
    Session _evenSession; address _even; 
    Session _oddSession;  address _odd;
    uint constant total = 2;
    uint _count;

    uint public step;
    mapping(address => uint) finished_step;

    event StartSession(Session);

    function Bsp() public {
        // first count is for joiners
        _count = total;
    }

    function joinEven() public {
        address client = msg.sender;
        require(_even == address(0x0));
        _even = client;
        _evenSession = new Session(_even, this);
        _count--;
        StartSession(_evenSession);
    }

    function done() public {
        address subserver = msg.sender;
        require(subserver == _even || subserver == _odd);
        require(finished_step[subserver] == step - 1);
        finished_step[subserver] = step;
        require(subserver == address(_evenSession));
        _count--;
        //updateGlobal(_evenState);
    }

    function next() public {
        require(_count == 0);
        _count = total;
        step++;
    }
}

contract Session {
  address _client;
  Bsp _server;

  bytes32 _step_1_h;
  bool _step_2_choice;

  function Session(address client, Bsp server) public { 
    _client = client;
    _server = server;
  }

  function step_1(bytes32 h) public {
    require(_server.step() == 1);
    require(msg.sender == _client);
    
    _step_1_h = h;

    _server.done();
  }

  function step_2(bool choice, uint256 salt) public {
    require(_server.step() == 2);
    require(msg.sender == _client);

    require(keccak256(choice, salt, msg.sender) == _step_1_h);
    delete _step_1_h;
    _step_2_choice = choice;

    _server.done();
  }
}
