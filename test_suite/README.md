# CIL to Promela Converter Test Suite

This test suite evaluates and improves the CIL-to-Promela converter through systematic testing and adaptive learning.

## Test Suite Structure

```
test_suite/
├── basic/              # Basic language features
│   ├── variables.cil   # Variable declarations and types
│   ├── arithmetic.cil  # Arithmetic operations
│   ├── conditionals.cil # If statements
│   └── loops.cil       # Loop constructs
├── intermediate/       # Intermediate features
│   ├── functions.cil   # Function definitions and calls
│   ├── arrays.cil      # Array handling
│   ├── structs.cil     # Struct definitions and usage
│   └── pointers.cil    # Basic pointer operations
├── advanced/           # Advanced features
│   ├── heap.cil        # Dynamic memory allocation
│   ├── linked_list.cil # Linked data structures
│   ├── oop.cil         # Object-oriented patterns
│   └── multithreading.cil # Concurrent execution
├── verification/       # Verification-specific tests
│   ├── assertions.cil  # Assertion verification
│   ├── atomic.cil      # Atomic sections
│   ├── ltl.cil         # LTL property verification
│   └── deadlock.cil    # Deadlock detection tests
├── expected/           # Expected correct Promela outputs
│   └── [matching .pml files for each test]
├── results/            # Test run results
├── test_runner.py      # Test execution script
└── adaptive_learner.py # Adaptive model improvement script
```

## Testing Approach

1. **Unit Tests**: Each test file focuses on specific language features or verification scenarios.
2. **Golden Tests**: Expected Promela outputs provide a reference for correctness.
3. **Regression Tests**: Ensures previously fixed issues don't reappear.
4. **Performance Tests**: Measures conversion time and quality.

## Adaptive Learning Process

1. **Error Collection**: Gather errors and failures from test runs
2. **Pattern Recognition**: Identify common error patterns
3. **Prompt Refinement**: Automatically refine conversion and error-fixing prompts
4. **Validation**: Verify improvements through test suite
5. **Continuous Integration**: Automated testing on each code change

## Metrics

- **Syntax Success Rate**: Percentage of tests producing valid Promela
- **Semantic Correctness**: Percentage of tests matching expected output
- **Verification Success**: Percentage of tests passing SPIN verification
- **Conversion Time**: Time required for conversion process
- **Error Resolution Rate**: Percentage of errors successfully fixed

## Usage

```bash
# Run all tests
python test_runner.py

# Run specific test category
python test_runner.py --category basic

# Run with adaptive learning
python test_runner.py --adapt

# Analyze results and update prompts
python adaptive_learner.py --results results/latest.json
``` 