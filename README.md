# Vegas: A Domain-Specific Language for Game-Theoretically Analyzed Blockchain-Based Games

Vegas (VErified Game Analysis and Synthesis) is a research tool that provides a unified language for specifying multi-party games with economic incentives, automatic translation to game-theoretic models, and smart contract generation.

## Overview

Vegas allows you to specify strategic interactions between multiple parties, including:
- Players joining with deposits
- Sequential and simultaneous moves
- Hidden information and reveal mechanisms
- Conditional payouts based on player actions

From a single Vegas specification, the tool generates:
- **Extensive form games** (Gambit EFG format) for game-theoretic analysis
- **Solidity smart contracts** for blockchain deployment

## Language Features

### Core Constructs

- **Type declarations**: Define custom types as subsets or ranges of integers
- **Join**: Players enter the game with deposits
- **Yield**: Players make moves (public or hidden)
- **Reveal**: Players reveal previously hidden information
- **Withdraw**: Specify payouts based on game outcomes

### Example: Monty Hall Game

```vegas
type door = {0, 1, 2}

join Host() $ 100;
join Guest() $ 100;
yield Host(car: hidden door);
yield Guest(d: door);
yield Host(goat: door) where Host.goat != Guest.d;
yield Guest(switch: bool);
reveal Host(car: door) where Host.goat != Host.car;
withdraw (Host.car != null && Guest.switch != null)
     ? { Guest -> ((Guest.d != Host.car) <-> Guest.switch) ? 20 : -20;  Host -> 0 }
     : (Host.car == null)
     ? { Guest -> 20;   Host -> -100 }
     : { Guest -> -100; Host -> 0 }
```

## Building and Running

### Build

```bash
# Generate ANTLR parser (assumes ANTLR is configured)
antlr4 -o ./generated/vegasGen -package vegasGen -listener -visitor -lib . ./Vegas.g4

# Compile Kotlin code
kotlinc src/vegas/*.kt -cp antlr-runtime.jar
```

### Run

```bash
kotlin -cp .:antlr-runtime.jar vegas.MainKt
```

This will process all example files and generate outputs in:
- `examples/gambit/` - Extensive form game files (.efg)
- `examples/solidity/` - Smart contract implementations (.sol)
- `examples/smt/` - SMT-LIB specifications (.z3) [experimental]
- `examples/scribble/` - Scribble protocol specifications (.scr) [experimental]

## Examples

The `examples/` directory contains several game specifications:

- **Bet.vg**: Simple betting game with random outcome
- **MontyHall.vg**: Classic Monty Hall problem with hidden information
- **Prisoners.vg**: Prisoner's dilemma
- **OddsEvens.vg**: Matching pennies variant
- **ThreeWayLottery.vg**: Three-player lottery with strategic selection
- **Puzzle.vg**: Number factorization puzzle

## Output Formats

### Gambit EFG

Generates extensive form game representations that can be analyzed using [Gambit](http://www.gambit-project.org/) game theory software to:
- Find Nash equilibria
- Analyze strategic dominance
- Compute expected payoffs

### Solidity Smart Contracts

Generates Ethereum smart contracts that implement the game mechanics including:
- Player registration with deposits
- Move validation and sequencing
- Commit-reveal schemes for hidden information
- Automatic payout distribution

**Note**: Generated contracts are proof-of-concept and not intended for production use.

## Project Structure

```
.
├── Vegas.g4                 # ANTLR grammar definition
├── src/vegas/
│   ├── Ast.kt               # Abstract syntax tree definitions
│   ├── AstTranslator.java   # ANTLR to AST translation
│   ├── Env.kt               # Environment for evaluation
│   ├── Gambit.kt            # Extensive form game generation
│   ├── Main.kt              # Entry point and orchestration
│   ├── Scribble.kt          # Scribble protocol generation (experimental)
│   ├── Smt.kt               # SMT-LIB generation (experimental)
│   ├── Solidity.kt          # Smart contract generation
│   ├── TypeChecker.kt       # Type system implementation
│   └── Utils.kt             # Utility functions
└── examples/
    ├── *.vg                 # Vegas source files
    ├── gambit/              # Generated .efg files
    └── solidity/            # Generated .sol files
```

## Language Syntax

### Types
```
type <name> = {<val1>, <val2>, ...}  // Enumerated type
type <name> = {<min>..<max>}         // Range type
```

### Game Flow
```
join <Role>(<params>) $ <deposit>;    // Player joins with deposit
yield <Role>(<params>);               // Player makes a move
reveal <Role>(<params>);              // Reveal hidden information
withdraw <outcome-expression>         // Specify payouts
```

### Expressions
- Arithmetic: `+`, `-`, `*`, `/`
- Comparison: `<`, `<=`, `>`, `>=`, `==`, `!=`
- Boolean: `&&`, `||`, `!`, `<->` (iff)
- Conditional: `condition ? ifTrue : ifFalse`
- Member access: `Role.field`
- Null check: `value == null`, `value != null`

## Limitations

- Type system supports only integers, booleans, and user-defined finite types
- No support for arrays or complex data structures
- Generated Solidity uses outdated compiler version (0.4.22)
- SMT and Scribble backends are incomplete/experimental
