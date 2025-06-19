# CIL to Promela Test Cases

This directory contains test cases for the CIL to Promela converter.

## Test Files

1. **simple.cil**: Basic functions and variables testing
   - Tests simple arithmetic operations
   - Tests conditional statements
   - Tests function calls

2. **array.cil**: Array handling
   - Tests array declarations
   - Tests array indexing
   - Tests iterating through arrays

3. **concurrency.cil**: Concurrency testing
   - Tests shared variables
   - Tests mutual exclusion (locks)
   - Tests interleaving of processes

4. **memory.cil**: Memory management
   - Tests memory allocation
   - Tests pointer manipulation
   - Tests memory deallocation

## Running the Tests

To run these tests with the agent, use:

```bash
python agent.py test_cases/simple.cil -o simple_output.pml
python agent.py test_cases/array.cil -o array_output.pml
python agent.py test_cases/concurrency.cil -o concurrency_output.pml
python agent.py test_cases/memory.cil -o memory_output.pml
``` 