// SPDX-License-Identifier: MIT
pragma solidity ^0.8.31;

/**
 * @title StateMachine
 * @notice Base contract for state machine pattern with step-based execution
 */
abstract contract StateMachine {
    uint256 public stmtIndex;
    uint256 public stepCount;

    error InvalidStep(uint256 expected, uint256 provided);
    error InvalidState(uint256 expected, uint256 current);
    error Unauthorized(address expected, address actual);

    modifier step(uint256 _stepCount) {
        if (stepCount != _stepCount) {
            revert InvalidStep(stepCount, _stepCount);
        }
        _;
        unchecked {
            stepCount++;
        }
    }

    modifier state(uint256 s) {
        if (s != stmtIndex) {
            revert InvalidState(s, stmtIndex);
        }
        _;
        unchecked {
            stmtIndex++;
        }
    }

    modifier stateNonInc(uint256 s) {
        if (s != stmtIndex) {
            revert InvalidState(s, stmtIndex);
        }
        _;
    }

    modifier onlyAddress(address expected) {
        if (msg.sender != expected) {
            revert Unauthorized(expected, msg.sender);
        }
        _;
    }
}

/**
 * @title JointDeclaration
 * @notice Contract for two parties to make a joint declaration
 */
contract JointDeclaration is StateMachine {
    event Declare(string message, address indexed partyA, address indexed partyB);

    address public partyA;
    address public partyB;

    error PartyAlreadySet();

    /// @notice Party A registers their participation
    function stmt_0_await_A(uint256 _stepCount)
    external
    step(_stepCount)
    stateNonInc(0)
    {
        if (partyA != address(0)) revert PartyAlreadySet();
        partyA = msg.sender;
        _incrementIfFinished();
    }

    /// @notice Party B registers their participation
    function stmt_0_await_B(uint256 _stepCount)
    external
    step(_stepCount)
    stateNonInc(0)
    {
        if (partyB != address(0)) revert PartyAlreadySet();
        partyB = msg.sender;
        _incrementIfFinished();
    }

    function _incrementIfFinished() private {
        if (partyA != address(0) && partyB != address(0)) {
            unchecked {
                stepCount++;
                stmtIndex++;
            }
        }
    }

    /// @notice Make the joint declaration
    function stmt_1_declare(uint256 _stepCount)
    external
    step(_stepCount)
    state(1)
    {
        emit Declare("are getting married", partyA, partyB);
    }

    /// @notice Finalize and destroy contract
    function end() external state(2) {
        selfdestruct(payable(msg.sender));
    }
}

/**
 * @title Puzzle
 * @notice A mathematical puzzle contract where solver must factorize a number
 */
contract Puzzle is StateMachine {
    event Declare(string message, address indexed solver);

    address public proposer;
    int256 public question;

    address public solver;
    int256 private solverM;
    int256 private solverN;

    error AlreadySet();
    error InvalidFactor();

    /// @notice Proposer submits a question (product to factorize)
    function stmt_0_await_Proposer(int256 q, uint256 _stepCount)
    external
    step(_stepCount)
    state(0)
    {
        if (proposer != address(0)) revert AlreadySet();
        proposer = msg.sender;
        question = q;
    }

    /// @notice Solver submits factors
    function stmt_1_await_Solver(int256 m, int256 n, uint256 _stepCount)
    external
    step(_stepCount)
    state(1)
    {
        if (m == 1 || n == 1) revert InvalidFactor();
        if (m * n != question) revert InvalidFactor();

        solver = msg.sender;
        solverM = m;
        solverN = n;
    }

    /// @notice Declare the winner
    function stmt_2_declare(uint256 _stepCount)
    external
    step(_stepCount)
    state(2)
    {
        emit Declare("solved the problem!", solver);
    }

    /// @notice Finalize and destroy contract
    function end() external state(3) {
        selfdestruct(payable(msg.sender));
    }
}

/**
 * @title PuzzlePayment
 * @notice Puzzle contract with payment reward for solver
 */
contract PuzzlePayment is StateMachine {
    event Declare(string message, address indexed solver);
    event PaymentSent(address indexed to, uint256 amount);

    address public proposer;
    int256 public question;
    uint256 public reward;

    address public solver;
    int256 private solverM;
    int256 private solverN;

    error InvalidFactor();

    /// @notice Proposer submits question with payment
    function stmt_0_await_Proposer(int256 q, uint256 _stepCount)
    external
    payable
    step(_stepCount)
    state(0)
    {
        proposer = msg.sender;
        reward = msg.value;
        question = q;
    }

    /// @notice Solver submits factors
    function stmt_1_await_Solver(int256 m, int256 n, uint256 _stepCount)
    external
    step(_stepCount)
    state(1)
    {
        if (m == 1 || n == 1) revert InvalidFactor();
        if (m * n != question) revert InvalidFactor();

        solver = msg.sender;
        solverM = m;
        solverN = n;
    }

    /// @notice Pay the solver
    function stmt_2_pay(uint256 _stepCount)
    external
    step(_stepCount)
    state(2)
    {
        uint256 amount = reward;
        reward = 0;

        (bool success,) = solver.call{value: amount}("");
        require(success, "Transfer failed");

        emit PaymentSent(solver, amount);
    }

    /// @notice Finalize and destroy contract
    function end() external state(3) {
        selfdestruct(payable(msg.sender));
    }
}

/**
 * @title CommitRevealGame
 * @notice Simultaneous game using commit-reveal scheme
 */
contract CommitRevealGame is StateMachine {
    event Declare(string message, address indexed winner);

    address public evenPlayer;
    bytes32 public evenCommitment;
    bool public evenChoice;
    bool public evenRevealed;

    address public oddPlayer;
    bytes32 public oddCommitment;
    bool public oddChoice;
    bool public oddRevealed;

    error AlreadyCommitted();
    error InvalidReveal();
    error NotRevealed();

    /// @notice Even player commits their choice
    function stmt_0_commit_Even(bytes32 commitment, uint256 _stepCount)
    external
    step(_stepCount)
    stateNonInc(0)
    {
        if (evenPlayer != address(0)) revert AlreadyCommitted();
        evenPlayer = msg.sender;
        evenCommitment = commitment;
        _incrementIfBothCommitted();
    }

    /// @notice Odd player commits their choice
    function stmt_0_commit_Odd(bytes32 commitment, uint256 _stepCount)
    external
    step(_stepCount)
    stateNonInc(0)
    {
        if (oddPlayer != address(0)) revert AlreadyCommitted();
        oddPlayer = msg.sender;
        oddCommitment = commitment;
        _incrementIfBothCommitted();
    }

    function _incrementIfBothCommitted() private {
        if (evenPlayer != address(0) && oddPlayer != address(0)) {
            unchecked {
                stepCount++;
                stmtIndex++;
            }
        }
    }

    /// @notice Even player reveals their choice
    function stmt_1_reveal_Even(bool choice, bytes32 salt, uint256 _stepCount)
    external
    onlyAddress(evenPlayer)
    step(_stepCount)
    stateNonInc(1)
    {
        if (keccak256(abi.encodePacked(choice, salt)) != evenCommitment) {
            revert InvalidReveal();
        }
        evenChoice = choice;
        evenRevealed = true;
        _incrementIfBothRevealed();
    }

    /// @notice Odd player reveals their choice
    function stmt_1_reveal_Odd(bool choice, bytes32 salt, uint256 _stepCount)
    external
    onlyAddress(oddPlayer)
    step(_stepCount)
    stateNonInc(1)
    {
        if (keccak256(abi.encodePacked(choice, salt)) != oddCommitment) {
            revert InvalidReveal();
        }
        oddChoice = choice;
        oddRevealed = true;
        _incrementIfBothRevealed();
    }

    function _incrementIfBothRevealed() private {
        if (evenRevealed && oddRevealed) {
            unchecked {
                stepCount++;
                stmtIndex++;
            }
        }
    }

    /// @notice Declare winner
    function stmt_2_declare(uint256 _stepCount)
    external
    step(_stepCount)
    state(2)
    {
        if (!evenRevealed || !oddRevealed) revert NotRevealed();
        address winner = (evenChoice == oddChoice) ? evenPlayer : oddPlayer;
        emit Declare("won", winner);
    }

    /// @notice Finalize and destroy contract
    function end() external state(3) {
        selfdestruct(payable(msg.sender));
    }
}

/**
 * @title SimpleAuction
 * @notice Basic auction contract with minimum price
 */
contract SimpleAuction is StateMachine {
    event NewBid(address indexed bidder, uint256 amount);
    event AuctionEnded(address indexed winner, uint256 amount);

    address public owner;
    uint256 public minimumBid;

    address public highestBidder;
    uint256 public highestBid;

    mapping(address => uint256) public pendingReturns;

    error BidTooLow(uint256 required);

    /// @notice Owner initializes auction
    function stmt_0_await_Owner(uint256 minimum, uint256 _stepCount)
    external
    step(_stepCount)
    state(0)
    {
        owner = msg.sender;
        minimumBid = minimum;
        highestBid = minimum;
    }

    /// @notice Submit a bid
    function stmt_1_bid(uint256 _stepCount)
    external
    payable
    step(_stepCount)
    stateNonInc(1)
    {
        if (msg.value <= highestBid) {
            revert BidTooLow(highestBid + 1);
        }

        if (highestBidder != address(0)) {
            pendingReturns[highestBidder] += highestBid;
        }

        highestBidder = msg.sender;
        highestBid = msg.value;

        emit NewBid(msg.sender, msg.value);

        unchecked {
            stepCount++;
        }
    }

    /// @notice Owner stops the auction
    function stmt_1_stop(uint256 _stepCount)
    external
    onlyAddress(owner)
    step(_stepCount)
    state(1)
    {
        stmtIndex = 2;
        emit AuctionEnded(highestBidder, highestBid);
    }

    /// @notice Withdraw overbid funds
    function withdraw() external {
        uint256 amount = pendingReturns[msg.sender];
        if (amount > 0) {
            pendingReturns[msg.sender] = 0;
            (bool success,) = msg.sender.call{value: amount}("");
            require(success, "Withdrawal failed");
        }
    }

    /// @notice Finalize and destroy contract
    function end() external state(2) {
        selfdestruct(payable(owner));
    }
}
