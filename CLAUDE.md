# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Spin is an explicit-state logic model checking tool for formal verification of multi-threaded software and concurrent systems. It uses the ProMeLa (Process Meta Language) specification language and can generate C verifier code for exhaustive state-space exploration.

## Build Commands

```bash
# Build spin executable
make

# Install to /usr/local/bin (requires appropriate permissions)
make install

# Clean build artifacts
make clean

# Build with strict warnings
make strict
```

Build configuration is in `Src/makefile`. The build requires gcc (or compatible C compiler) and yacc/bison.

## Testing

```bash
# Run automated test suite
make test

# Run tests with coverage report
make coverage
# Open coverage/html/index.html for detailed report

# Quick coverage summary
make coverage-summary
```

The test suite (`test/run_tests.sh`) automates the verification workflow documented in `Examples/README_tests.txt`.

## Static Analysis

```bash
# Run cppcheck
make cppcheck

# Generate XML report
make cppcheck-xml

# Run clang static analyzer
make scan-build
```

## CI/CD

GitHub Actions workflows in `.github/workflows/`:
- `ci.yml` - Builds on Linux/macOS/Windows, runs tests, coverage, and static analysis
- `release.yml` - Creates releases with binaries when tags are pushed
- `nightly.yml` - Daily builds with pre-release binaries

## Architecture

### Parser & Core Data Structures
- `spin.y` - YACC grammar for ProMeLa language
- `spinlex.c` - Lexical analyzer
- `spin.h` - Core data structures (Lextok, Symbol, Element, Sequence, RunList, ProcList, Queue, FSM_state)

### Code Generation Pipeline (pangen modules)
- `pangen1.c/h` - Process code generation, initialization
- `pangen2.c/h` - Variable tracking and state management
- `pangen3.c/h` - Statement code generation
- `pangen4.c/h` - Message queue handling
- `pangen5.c/h` - Dataflow analysis and slicing
- `pangen6.c/h` - Optimization
- `pangen7.c/h` - Advanced code generation

Note: `pangen*.h` files contain C code templates that get embedded in generated verifiers, not traditional headers.

### LTL Processing
- `tl_parse.c` - LTL formula parsing
- `tl_lex.c` - LTL lexical analysis
- `tl_trans.c` - LTL to Buchi automata transformation
- `tl_buchi.c` - Buchi automaton generation

### Verification Engine
- `main.c` - Driver and command-line parsing
- `flow.c` - Control flow analysis
- `sched.c` - Process scheduling logic
- `run.c` - Runtime simulation execution

### Workflow
1. Parse ProMeLa specification into AST
2. Build symbol table and validate semantics
3. Perform static analysis (slicing, dataflow)
4. Generate C verifier code (`pan.c`)
5. User compiles verifier with problem-specific flags
6. Verifier executes exhaustive state space search
