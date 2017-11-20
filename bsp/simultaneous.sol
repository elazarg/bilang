pragma solidity ^0.4.17;

contract Bsp {
    Session _evenSession; address _even; 
    Session _oddSession;  address _odd;
    uint constant total = 2;
    uint _count;

    uint public step;
    mapping(address => uint) finished_step;

    function Bsp(Session evenSession, Session oddSession) public {
        _evenSession = evenSession;
        _oddSession = oddSession;
        _count = 0;
        next();
    }

    function joinEven() public {
        require(_even == address(0x0));
        _even = msg.sender;
        _evenSession = new Session(_even, this);
    }

    function done() public {
        require(msg.sender == _even || msg.sender == _odd);
        require(finished_step[msg.sender] == step - 1);
        finished_step[msg.sender] = step;
        require(msg.sender == address(_evenSession));
        _count--; 
        //updateGlobal(_evenState);
    }

    function next() public {
        require(_count == 0);
        _count = 2;
    }
}

contract Session {
  address _client;
  Bsp _server;

  uint256 _step_1_h;
  bool _step_2_choice;

  function Session(address client, Bsp server) public { 
    _client = client;
    _server = server;
  }

  function step_1(uint256 h) public {
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
