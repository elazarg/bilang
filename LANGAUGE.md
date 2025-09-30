# BiLang Language Reference

## Overview

BiLang is a domain-specific language for specifying strategic games and multi-party protocols with **distribution transparency**. Programs are written as sequential game descriptions that compile to distributed implementations preserving game-theoretic properties.

### Design Philosophy

1. **Abstraction over Distribution**: Write game logic without thinking about distributed execution details (commit-reveal, timeouts, griefing)
2. **Compiler-Managed Protocols**: The compiler automatically generates cryptographic protocols (commitments, reveals) and coordination mechanisms
3. **Explicit Failure Handling**: When distribution cannot be hidden (player abandonment, timeouts), the language forces explicit handling via null checks
4. **Multi-Backend Compilation**: The same specification compiles to execution (Solidity), analysis (Gambit), verification (SMT), and documentation (Scribble)

## Language Semantics

### Core Execution Model

A BiLang program describes a **sequential game tree** executed by multiple parties:

```
program ::= typeDec* ext

ext ::= 'join' query+ ';' ext          # Player entry
      | 'yield' query+ ';' ext         # Public moves
      | 'reveal' query+ ';' ext        # Reveal hidden info
      | 'random' query+ ';' ext        # Chance moves  
      | 'withdraw' outcome             # Terminal payoffs

query ::= role '(' varDec* ')' ('$' deposit)? ('where' condition)?
```

**Intuition**: A program specifies a protocol where:
- Players **join** (possibly depositing funds)
- Players **yield** information (public or hidden)
- Hidden information is later **revealed** with cryptographic verification
- The game terminates with **withdraw** specifying payoffs

### Abstract Semantics (Ideal World)

In the abstract model, execution is **centralized and sequential**:

1. **Join Phase**: Players register and post deposits to a trusted coordinator
2. **Move Sequence**: For each `yield` or `reveal`:
    - The coordinator asks the player for their move
    - The player responds immediately
    - State updates atomically
3. **Terminal Phase**: Coordinator computes outcome and distributes payoffs

**Guarantees in Ideal World**:
- No player can see others' hidden information before it's revealed
- All moves happen in sequence
- No player can abandon (they always respond)
- Outcome computation is instantaneous

### Concrete Semantics (Real World / Blockchain)

The compiler transforms the abstract program into a **distributed protocol**:

1. **Commit-Reveal for Hidden Information**:
   ```
   yield Alice(choice: hidden int)
   ```
   Becomes:
   ```solidity
   // Step 1: Alice commits hash
   function join_commit_Alice(bytes32 commitment) { ... }
   
   // Step 2: Alice reveals preimage
   function join_Alice(int choice, uint256 salt) {
       require(keccak256(choice, salt) == commitment);
   }
   ```

2. **Step-Based State Machine**:
   Each `yield`/`reveal` becomes a contract function callable at a specific step

3. **Timeout Protection**:
   After `STEP_TIME`, any party can force progression (opponent forfeits)

4. **Null Values for Abandonment**:
   If a player doesn't submit by timeout, their variables are `null`

**Real World Challenges**:
- **Timing**: Players act asynchronously
- **Abandonment**: Players may not submit moves
- **Privacy**: Must use cryptography to hide information
- **Atomicity**: State updates are explicit transactions

---

## Distribution Transparency

### What the Compiler Handles Automatically

 **Commit-Reveal Protocols**

```bilang
join Host() $ 100;
join Guest() $ 100;
yield Host(car: hidden door);  // Compiler generates commitment scheme
yield Guest(choice: door);      // Public, no commitment needed
reveal Host(car: door);         // Compiler generates reveal + verification
```

Generated Solidity:
- `join_commit_Host(bytes32 c)` - commitment phase
- `join_Host(door car, uint256 salt)` - reveal with verification
- Automatic `keccak256` verification

 **Step Sequencing**

```bilang
yield A(x: int);
yield B(y: int);
```

Becomes enforced sequence:
```solidity
function yield_A(int x) at_step(0) { ... }
function yield_B(int y) at_step(1) { ... }
```

 **Information Flow Typing**

```bilang
reveal Host(car: door) where Host.car != Host.goat;
```

Type checker ensures:
- `Host.car` was declared `hidden` earlier
- Reveal type matches original hidden type
- Where clause doesn't leak information

 **Deposit Management**

```bilang
join Player() $ 100;
withdraw { Player -> 150 }
```

Generates:
```solidity
balanceOf[msg.sender] = msg.value;  // On join
payable(msg.sender).call{value: 150}("");  // On withdraw
```

### What the Programmer Must Handle

 **Player Abandonment**

The language **forces** explicit null handling:

```bilang
withdraw (Host.car != null && Guest.choice != null)
    ? { Host -> 0; Guest -> 100 }   // Normal case
    : { Host -> -100; Guest -> 100 } // Griefing penalty
```

**Why**: The compiler cannot decide griefing penalties - this is a game design choice.

**Type System Enforcement**:
- `Member` access has type `Opt[T]` if player might abandon
- Using it in arithmetic without null check is a **type error**
- Must use `isDefined()` or ternary with null check

 **Step Timeout Configuration** (Current Limitation)

Currently hardcoded:
```kotlin
uint256 public constant STEP_TIME = 500;
```

**Future**: Should be configurable per-step based on complexity:
```bilang
yield Host(strategy: complex_type) timeout 3600;  // 1 hour
yield Guest(response: bool) timeout 300;          // 5 minutes
```

 **Griefing Prevention Design**

The language provides mechanisms but not policy:

```bilang
// Option 1: Full forfeit
withdraw Alice.choice != null 
    ? { Alice -> 100; Bob -> 0 }
    : { Alice -> 0; Bob -> 100 }

// Option 2: Proportional penalty
withdraw Alice.choice != null && Bob.choice != null
    ? compute_outcome(Alice.choice, Bob.choice)
    : { Alice -> -100; Bob -> -100 }  // Both lose deposits

// Option 3: Graduated penalties
withdraw 
    let timeout_block = current_block() in
    let penalty = min(100, timeout_block - deadline) in
    { Alice -> -penalty; Bob -> penalty }
```

---

## Type System

### Purpose

The type system ensures:
1. **Information Flow Security**: Hidden values can't leak before reveal
2. **Protocol Correctness**: Reveals match commitments, or punished
3. **Robustness**: Abandonment is explicitly handled
4. **Game-Theoretic Properties**: Constraints are enforced

### Type Hierarchy

```
TypeExp ::= int                    # Unbounded integers
          | bool                   # Booleans
          | {v1, v2, ...}         # Finite subset
          | {min..max}            # Integer range
          | TypeId                # User-defined type
          | hidden T              # Private information
          | role                  # Role reference
```

### Subtyping Rules

```
{1, 2, 3} <: int
{1..10} <: int
{1, 2, 3} <: {1..5}  (if all elements in range)

hidden T <: hidden T' if T <: T'  (covariant)
```

### Information Flow

**Security Property**: Hidden values cannot flow to public contexts before reveal

```bilang
yield Host(secret: hidden int);
yield Guest(guess: int) where Guest.guess == Host.secret;  // TYPE ERROR!
```

Error: Cannot compare hidden and public values

**Correct Version**:
```bilang
yield Host(secret: hidden int);
yield Guest(guess: int);
reveal Host(secret: int);  // Now public
withdraw { Guest -> (Guest.guess == Host.secret ? 100 : 0) }
```

### Null Handling (Abandonment)

**Rule**: Any `yield` or `reveal` creates `Opt[T]` if timeout possible

```bilang
yield Alice(x: int);
withdraw { Alice -> Alice.x + 10 }  // TYPE ERROR: Alice.x : Opt[int]
```

**Fix**: Explicit null check
```bilang
withdraw Alice.x != null 
    ? { Alice -> Alice.x + 10 }
    : { Alice -> -100 }  // Penalty for abandoning
```

**Type Checking**:
```
isDefined(e) : bool     if e : Opt[T]
e != null : bool        if e : Opt[T]

e : T                   in context where e : Opt[T] is checked != null
```

---

## Compilation Strategy

### From Abstract to Concrete

The compiler performs a **semantics-preserving transformation**:

```
Abstract Program → Information Flow Analysis → Protocol Synthesis → Code Generation
                                                                  ├→ Solidity
                                                                  ├→ Gambit
                                                                  ├→ SMT-LIB
                                                                  └→ Scribble
```

### Phase 1: Type Checking & Analysis

**Input**: BiLang AST  
**Output**: Typed AST + Information Flow Graph

1. Resolve custom types
2. Build role environment (who's in scope when)
3. Track hidden vs public information
4. Enforce commit constraints upon reveal
5. Check null handling

**Example**:
```bilang
type door = {0, 1, 2}
join Host();
yield Host(car: hidden door);  // Host.car : hidden {0,1,2}
reveal Host(car: door);         // Host.car : {0,1,2} (now public)
```

Type environment:
```
After join:   Γ = {Host: role}
After yield:  Γ = {Host: role, Host.car: hidden {0,1,2}}
After reveal: Γ = {Host: role, Host.car: Opt[{0,1,2}]}  // Opt due to timeout
```

### Phase 2: Protocol Synthesis

**Commitment Synthesis**:

For each `query` with hidden parameters:
```bilang
yield Role(p1: hidden T1, p2: T2, p3: hidden T3)
```

Generate:
1. Commitment function: `Role_commit(hash)`
2. Reveal function: `Role_reveal(T1 p1, T2 p2, T3 p3, uint256 salt)`
3. Verification: `require(keccak256(p1, p3, salt) == stored_hash)`

**Step Linearization**:

```bilang
join A(); join B();
yield A(x: int) B(y: int);
yield A(x2: int);
```

Becomes:
```
Step 0: join_A(), join_B()
Step 1: yield_A_0(x), yield_B_0(y)
Step 2: advance_step_1()
Step 3: yield_A_1(x2)
```

### Phase 3: Code Generation

#### Solidity Backend

**State Variables**:
```solidity
uint256 public step;                    // Current step
mapping(address => Role) public role;   // Role assignments
mapping(address => uint256) balanceOf;  // Deposits

// For each Role.param:
T public Role_param;
bool public Role_param_done;
```

**Functions**:
```solidity
// Join
function join_Role() payable at_step(S) {
    require(msg.value == DEPOSIT);
    role[msg.sender] = Role.R;
    balanceOf[msg.sender] = msg.value;
}

// Yield (public)
function yield_Role_step(T param) by(Role.R) at_step(S) {
    require(!done_Role_step);
    Role_param = param;
    Role_param_done = true;
    done_Role_step = true;
}

// Yield (hidden)
function yield_commit_Role(bytes32 c) by(Role.R) at_step(S) {
    require(!halfStep_Role);
    commits_Role[msg.sender] = c;
}

function yield_Role(T param, uint256 salt) by(Role.R) at_step(S) {
    require(keccak256(param, salt) == commits_Role[msg.sender]);
    Role_param = param;
    Role_param_done = true;
}

// Withdraw
function withdraw_Role() by(Role.R) at_step(FINAL) {
    int256 payout = /* outcome expression */;
    balanceOf[msg.sender] = 0;
    (bool ok,) = payable(msg.sender).call{value: uint(payout)}("");
    require(ok);
}
```

#### Gambit Backend

Converts to extensive-form game tree:

```bilang
join A(); join B();
yield A(c: bool) B(c: bool);
withdraw { A -> (A.c <-> B.c ? 10 : -10), B -> ... }
```

Becomes:
```gambit
EFG 2 R "Game" { "A" "B" }
p "" 1 1 "" { "A.c=true" "A.c=false" } 0
  p "" 2 1 "" { "B.c=true" "B.c=false" } 0
    t "" 1 "" { 10 10 }
    t "" 2 "" { -10 -10 }
  p "" 2 2 "" { "B.c=true" "B.c=false" } 0
    t "" 3 "" { -10 -10 }
    t "" 4 "" { 10 10 }
```

This enables:
- Nash equilibrium computation
- Subgame perfect equilibrium
- Strategy dominance analysis

#### SMT Backend

Generates verification conditions:

```bilang
yield A(x: int) where x > 0;
withdraw { A -> x * 2 }
```

Becomes:
```smt
(declare-const A_x Int)
(declare-const A_x_done Bool)

(assert (=> A_x_done (> A_x 0)))  ; where clause

(define-fun A_outcome () Int
  (ite A_x_done (* A_x 2) -100))  ; with timeout penalty

; Properties to verify:
(assert (=> A_x_done (>= A_outcome 0)))  ; Individual rationality
(check-sat)
```

---

## Game-Theoretic Properties

### Properties Expressible in BiLang

**1. Budget Balance**:
```bilang
// Zero-sum game
withdraw { A -> x; B -> (- x) }
```

Compiler can verify: `sum(payoffs) = sum(deposits)`

**2. Individual Rationality**:
```bilang
join Player() $ 100;
withdraw Player.choice != null
    ? { Player -> max(0, outcome(Player.choice)) }
    : { Player -> -100 }
```

Property: `Expected[payout] >= -deposit` if player plays optimally

**3. Incentive Compatibility**:
```bilang
yield Bidder(bid: int) where bid >= 0;
withdraw { 
    Winner -> (valuation - price); 
    Loser -> 0 
}
```

Can verify truthful bidding is dominant strategy (via SMT backend)

**4. Collusion Resistance**:

Hard to express directly, but can encode constraints:
```bilang
yield A(c: int) B(c: int) where A.c != B.c;  // Force different choices
```

### Preservation Across Compilation

**Theorem (Informal)**: If the abstract program satisfies a game-theoretic property, the compiled Solidity contract preserves it *assuming all parties are rational*.

**Caveats**:
1. **Griefing**: Irrational players can reduce others' payoffs by abandoning
2. **Gas Costs**: Not modeled in abstract semantics
3. **Front-Running**: Not modeled (requires additional analysis)

**Mitigation**:
```bilang
// Explicit griefing penalties
withdraw Alice.c != null && Bob.c != null
    ? normal_outcome(Alice.c, Bob.c)
    : (Alice.c == null ? { Alice -> -100; Bob -> 0 }
                       : { Alice -> 0; Bob -> -100 })
```

This ensures:
- Rational players prefer to play
- Property holds on "no abandonment" path
- Abandonment has explicit consequences

---

## Examples with Commentary

### Example 1: Commit-Reveal (Coin Flip)

**Abstract**:
```bilang
join Alice() $ 10;
join Bob() $ 10;
yield Alice(c: hidden bool);  // Alice commits to a bit
yield Bob(c: bool);            // Bob guesses
reveal Alice(c: bool);         // Alice reveals
withdraw Alice.c != null && Bob.c != null
    ? { Alice -> (Alice.c <-> Bob.c ? 20 : 0);
        Bob   -> (Alice.c <-> Bob.c ? 0 : 20) }
    : (Alice.c == null ? { Alice -> -10; Bob -> 10 }
                       : { Alice -> 10; Bob -> -10 })
```

**What the Compiler Does**:
1. Generates `Alice_commit(bytes32 hash)` automatically
2. Generates `Alice_reveal(bool c, uint256 salt)` with verification
3. Enforces step ordering: commit → guess → reveal
4. Handles timeout: if Alice doesn't reveal, she forfeits

**What the Programmer Does**:
1. Specifies griefing penalties (forfeit deposit)
2. Ensures outcome is fair when both play

**Property Preserved**: Alice cannot change her bit after seeing Bob's guess (binding commitment)

### Example 2: Multi-Party Lottery

**Abstract**:
```bilang
type choice = {1, 2, 3}

join Issuer(c: choice) $ 10
     Alice(c: choice) $ 10
     Bob(c: choice) $ 10;

withdraw (Alice.c == null || Bob.c == null)
    ? { Alice -> -10; Bob -> -10; Issuer -> 20 }
    : (Issuer.c == null)
    ? { Alice -> 20; Bob -> -10; Issuer -> -10 }
    : ((Issuer.c + Alice.c + Bob.c) % 3 == 0)
    ? { Alice -> 20; Bob -> -10; Issuer -> -10 }
    : ((Issuer.c + Alice.c + Bob.c) % 3 == 1)
    ? { Alice -> -10; Bob -> 20; Issuer -> -10 }
    : { Alice -> -10; Bob -> -10; Issuer -> 20 }
```

**What the Compiler Does**:
1. All three `join` are conceptually simultaneous (same step). No explicit commit-reveal needed

**What the Programmer Does**:
1. Specifies lottery rule (sum mod 3)
2. Handles all abandonment cases explicitly
3. Ensures issuer can also lose (prevents collusion)

**Property**: Budget balanced (`sum = 10+10+10-10-10-10 = 0`)

### Example 3: Monty Hall (Information Flow)

**Abstract**:
```bilang
type door = {0, 1, 2}

join Host() $ 100;
join Guest() $ 100;

yield Host(car: hidden door);                    // Host hides car
yield Guest(choice: door);                       // Guest picks
yield Host(goat: door)                           // Host reveals goat
    where Host.goat != Guest.choice              // Can't reveal guest's door
       && Host.goat != Host.car;                 // Can't reveal car

yield Guest(switch: bool);                       // Guest switches?
reveal Host(car: door);                          // Host reveals car location

withdraw (Host.car != null && Host.goat != null && Guest.switch != null)
    ? { Guest -> ((Guest.choice != Host.car) <-> Guest.switch ? 20 : -20);
        Host  -> 0 }
    : (Host.car == null || Host.goat == null)
    ? { Guest -> 20; Host -> -100 }              // Host abandoned
    : { Guest -> -100; Host -> 0 }               // Guest abandoned
```

**What the Compiler Does**:
1. Generates commit for `Host.car` (hidden)
2. Enforces `where` clause: Host can't reveal invalid goat
3. Type-checks reveal: `Host.car` matches hidden type
4. Prevents Host from seeing `Guest.switch` before revealing

**What the Programmer Does**:
1. Specifies game rules (switching logic)
2. Handles abandonment with penalties
3. Ensures Host is penalized for invalid goat reveal (via where clause)

**Property**: Host learns nothing about `Guest.switch` before revealing `car` (information flow security)

---

## Advanced Features

### Where Clauses: Constrained Moves

```bilang
yield Player(x: int) where x >= 0 && x <= 100;
```

**Semantics**: The move is invalid if the constraint fails

**Compilation**:
```solidity
function yield_Player(int x) {
    require(x >= 0 && x <= 100, "where clause failed");
    Player_x = x;
}
```

**Use Cases**:
- Valid move constraints (chess: knight moves)
- Information flow constraints (Monty Hall: goat ≠ car)
- Economic constraints (bid ≥ reserve price)

### Let Bindings: Outcome Computation

```bilang
withdraw 
    let total_bids = Alice.bid + Bob.bid in
    let winner = (Alice.bid > Bob.bid ? Alice : Bob) in
    {
        Alice -> (Alice.bid > Bob.bid ? (value - Alice.bid) : 0);
        Bob   -> (Bob.bid > Alice.bid ? (value - Bob.bid) : 0)
    }
```

**Semantics**: Named intermediates for complex outcomes

**Compilation**: Inlined in Solidity (no extra storage)

### Custom Types: Domain Modeling

```bilang
type card = {1..52}
type suit = {0, 1, 2, 3}  // Hearts, Diamonds, Clubs, Spades

function suit_of(c: card) -> suit { (c - 1) / 13 }
```

**Future**: User-defined functions in outcomes

---

## Limitations & Future Work

### Current Limitations

1. **No Loops**: Can't express repeated games directly
    - Workaround: Unroll loops manually
    - Future: `repeat N times { ... }`

2. **Fixed Timeout**: All steps have same timeout
    - Future: Per-step timeout annotations

3. **No Partial Reveals**: Reveal is all-or-nothing
    - Future: `reveal Host(car: door) if condition`

4. **No Dynamic Roles**: Number of players fixed at compile time
    - Future: `join Player[n]` for variable player count

5. **No Encrypted Computation**: Hidden values must be revealed eventually
    - Future: ZK-SNARK backend for zero-knowledge proofs

### Research Directions

**1. Formal Semantics**

Define operational semantics with preservation theorem:
```
If ⊢ P : Game and P ⟹* v 
   then [[P]]_solidity preserves properties of v
```

**2. Optimizing Compiler**

- Gas optimization: minimize storage slots
- Commitment optimization: batch multiple hides
- Proof optimization: generate only necessary verification

**3. Advanced Cryptography**

- Threshold cryptography: M-of-N reveals
- Homomorphic encryption: compute on encrypted values
- Secure multi-party computation: no reveal needed

**4. Economic Analysis**

- Automatic mechanism design: compiler suggests griefing penalties
- Equilibrium computation: link Gambit backend to solver
- Collusion detection: analyze information flow for leaks

**5. Verification**

- Automated theorem proving: prove properties via SMT
- Simulation-based testing: Monte Carlo simulation
- Adversarial analysis: model malicious behavior

---

## FAQ

**Q: Why force null handling instead of automatic timeouts?**

A: Griefing penalties are a game design choice. A compiler can't decide if abandonment should result in:
- Full forfeit (harsh, may be unfair)
- Proportional penalty (complex to compute)
- Random outcome (may favor abandonee)

The language forces the programmer to make this explicit.

**Q: Why not use Solidity directly?**

A: Solidity is too low-level:
- Commit-reveal is error-prone (many contracts get it wrong)
- No static verification of game properties
- No automatic analysis (Nash equilibria, etc.)
- Information flow bugs are common

BiLang provides:
- Compiler-generated cryptographic protocols
- Static type checking for information flow
- Multi-backend compilation for analysis
- Game-theoretic property preservation

**Q: How do I handle complex timing (e.g., auction deadlines)?**

A: Current workaround:
```bilang
yield Bidder(bid: int, timestamp: int)
    where timestamp <= DEADLINE;
```

Future: First-class time:
```bilang
yield Bidder(bid: int) deadline block(1000);
```

**Q: Can I express partially observable games?**

A: Yes, via hidden information:
```bilang
type card = {1..52}

yield Dealer(hand1: hidden card, hand2: hidden card);
yield Player1(); // Player1 sees hand1 later
yield Player2(); // Player2 sees hand2 later

reveal Dealer(hand1: card) to Player1;  // Selective reveal (future feature)
reveal Dealer(hand2: card) to Player2;
```

**Q: How does this compare to Ivy/Simplicity/Pact?**

A:
- **Ivy**: Bitcoin scripts
- **Simplicity**: Low-level, no game abstractions
- **Pact**: General smart contracts, no game semantics

BiLang is specialized for strategic interactions with:
- Game-theoretic analysis (Gambit)
- Information flow typing (hidden types)
- Automatic protocol synthesis (commit-reveal)
- Client conformance checking (Scribble)

---

## Conclusion

BiLang achieves **game-analyzability** **distribution transparency** by:

1. **Abstracting Protocols**: Programmer writes sequential game logic; compiler generates distributed protocols
2. **Enforcing Robustness**: Type system forces explicit handling of abandonment
3. **Preserving Properties**: Compilation is semantics-preserving for game-theoretic guarantees
4. **Enabling Analysis**: Multi-backend compilation allows formal verification and equilibrium computation

The key insight: **Strategic games are naturally sequential**, but implementations are distributed. BiLang bridges this gap while maintaining the programmer's ability to reason about high-level properties.