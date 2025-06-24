# CToPromelaAgentic: AI-Powered C to Promela Converter

## Table of Contents   
1. [Overview](#1-overview)
2. [Core Features](#2-core-features)
3. [Implementation Architecture & Details](#3-implementation-architecture-details)
4. [Key Technologies Used](#4-key-technologies-used)
5. [System Requirements](#5-system-requirements)
6. [Installation and Setup](#6-installation-and-setup)
    1. [Obtain the Software](#61-obtain-the-software)
    2. [Python Environment Setup](#62-python-environment-setup)
    3. [Install Dependencies](#63-install-dependencies)
    4. [Install CIL (C Intermediate Language)](#64-install-cil-c-intermediate-language)
    5. [Install SPIN Model Checker](#65-install-spin-model-checker)
    6. [Google API Key Setup](#66-google-api-key-setup)
7. [Running the Application](#7-running-the-application)
    1. [GUI Mode (Recommended for Interactive Use)](#71-gui-mode-recommended-for-interactive-use)
    2. [Manual GUI Start (Alternative)](#72-manual-gui-start-alternative)
    3. [Command Line Mode (for Testing and Batch Processing)](#73-command-line-mode-for-testing-and-batch-processing)
8. [Using the GUI](#8-using-the-gui)
9. [Practical Usage Examples & Common Use Cases](#9-practical-usage-examples-common-use-cases)
    1. [Basic C Program Conversion](#91-basic-c-program-conversion)
    2. [Concurrency and Synchronization](#92-concurrency-and-synchronization)
    3. [Memory Safety Verification](#93-memory-safety-verification)
    4. [Real-World Application: Network Protocol Verification](#94-real-world-application-network-protocol-verification)
    5. [Common Verification Properties](#95-common-verification-properties)
    6. [Performance and Scalability Considerations](#96-performance-and-scalability-considerations)
10. [Project Structure](#10-project-structure)
11. [Potential Future Enhancements](#11-potential-future-enhancements)
12. [How to Contribute](#12-how-to-contribute)
13. [License](#13-license)

## 1. Overview

CToPromelaAgentic is an advanced AI-powered software tool designed to bridge the gap between C/C++ programming and formal verification. It automates the conversion of C/C++ source code, specifically through its C Intermediate Language (CIL) representation, into Promela (Process Meta Language). Promela is the input language for the SPIN (Simple Promela Interpreter) model checker, a widely used tool for verifying the correctness of distributed software systems.

### What the Project Does

**Core Functionality:**
- **Automated Code Translation**: Converts C/C++ code to Promela through a multi-stage process involving CIL preprocessing and AI-powered semantic translation
- **Formal Verification Enablement**: Makes it possible to formally verify C/C++ programs for properties like deadlock freedom, race conditions, memory safety, and custom assertions
- **Intelligent Error Handling**: Uses machine learning to identify, categorize, and automatically fix common conversion errors
- **Interactive Development Environment**: Provides a web-based GUI for easy file upload, conversion monitoring, and result analysis

**The Conversion Pipeline:**
1. **C/C++ → CIL**: Preprocesses C code into a simplified intermediate representation
2. **CIL → Promela**: Uses Google Gemini AI to intelligently translate CIL constructs to Promela
3. **Verification**: Validates the generated Promela code using SPIN model checker
4. **Error Correction**: Automatically identifies and fixes issues in the generated code
5. **Iterative Refinement**: Learns from errors to improve future conversions

**Why This Matters:**
The primary goal of CToPromelaAgentic is to make formal verification techniques accessible to software developers who may not be experts in formal methods. Traditional formal verification requires deep knowledge of specification languages and verification tools. This project eliminates that barrier by:
- Automatically handling the complex translation between programming paradigms
- Providing intelligent error diagnosis and correction
- Offering an intuitive interface for non-experts
- Learning from previous conversions to improve accuracy over time

This enables developers to formally verify critical properties of their C/C++ code, such as deadlock freedom, race condition absence, memory safety violations, and custom business logic assertions, using the robust capabilities of the SPIN model checker.

## 2. Core Features

CToPromelaAgentic offers a comprehensive suite of features to facilitate an efficient and accurate conversion process:

*   **Intelligent CIL to Promela Conversion**:
    *   Utilizes advanced AI (Google Gemini models) to understand the intent and structure of CIL code.
    *   Translates C control structures (if/else, loops, switch), data types, functions, and pointers into semantically equivalent Promela constructs.
    *   Handles common C idioms and patterns, aiming for a readable and verifiable Promela output.

*   **Sophisticated Error Handling and Learning**:
    *   Incorporates an `ErrorDatabase` to log, categorize, and learn from conversion errors.
    *   The system can identify patterns in erroneous CIL inputs or unsuccessful conversion attempts.
    *   Over time, it uses this knowledge to suggest fixes or automatically adapt its conversion strategies, improving accuracy with continued use.

*   **User-Friendly Graphical User Interface (GUI)**:
    *   A web-based GUI built with Streamlit provides an intuitive platform for interaction.
    *   Users can easily upload C or CIL files, configure conversion parameters, monitor progress, and view results.
    *   The GUI displays the original code, generated Promela, conversion logs, and any detected errors or applied fixes.

*   **SPIN Model Checker Integration Support**:
    *   The generated Promela code is structured to be compatible with the SPIN model checker.
    *   Facilitates the process of taking C code to a verifiable model, enabling formal analysis of system properties.

*   **Comprehensive Test Suite**:
    *   Includes a robust testing framework (`tests/test_unified.py`) with numerous test cases (`test_cases/` and `cil_test_files/`).
    *   Ensures the reliability and correctness of the conversion engine across a wide range of C constructs and scenarios.

*   **Adaptive Learning System**:
    *   The `ErrorDatabase` and associated logic in `core/error_database.py` contribute to an adaptive system.
    *   By analyzing past conversions, the tool refines its understanding of complex or ambiguous C patterns, leading to improved Promela generation over time.

*   **C to CIL Preprocessing**:
    *   Includes a `CtoCILConverter` module (`core/CtoCILConvertor.py`) that utilizes the CIL framework to preprocess C/C++ code into the simplified CIL format, which is then used for the main conversion task.

## 3. Implementation Architecture & Details

### 3.1. System Architecture

The CToPromelaAgentic system follows a modular, pipeline-based architecture:

```
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│   C/C++ Code    │───▶│   CIL Converter  │───▶│  CIL Representation │
└─────────────────┘    └──────────────────┘    └─────────────────┘
                                                          │
┌─────────────────┐    ┌──────────────────┐              │
│  Promela Code   │◀───│  AI Converter    │◀─────────────┘
└─────────────────┘    └──────────────────┘
          │                      ▲
          ▼                      │
┌─────────────────┐    ┌──────────────────┐
│  SPIN Verifier  │───▶│  Error Handler   │
└─────────────────┘    └──────────────────┘
          │                      │
          ▼                      ▼
┌─────────────────┐    ┌──────────────────┐
│ Verification    │    │  Error Database  │
│   Results       │    │   & Learning     │
└─────────────────┘    └──────────────────┘
```

### 3.2. Core Components Implementation

#### 3.2.1. CIL Converter (`core/CtoCILConvertor.py`)

**Purpose**: Transforms C/C++ code into CIL (C Intermediate Language) format for standardized processing.

**Key Implementation Details**:
- **Structure Analysis**: Parses C code to extract functions, global variables, structs, typedefs, and enums
- **Normalization Process**:
  - Variable declarations: `int x, y;` → `int x; int y;`
  - Function parameters: Handles complex parameter types including arrays and pointers
  - Control structures: Standardizes if/else, loops, and switch statements
  - Struct/array access: Normalizes member access and array indexing
  - Pointer operations: Simplifies pointer arithmetic and dereferencing

**Transformation Pipeline**:
```python
def convert(self, c_code: str) -> str:
    # 1. Preserve comments for context
    preprocessed_code = self._preserve_comments(c_code)
    
    # 2. Remove preprocessor directives (#include, #define, etc.)
    preprocessed_code = self._remove_preprocessor_directives(preprocessed_code)
    
    # 3. Analyze code structure (functions, variables, types)
    self._analyze_structure(preprocessed_code)
    
    # 4. Apply CIL transformations
    cil_code = self._transform_to_cil(preprocessed_code)
    
    return cil_code
```

#### 3.2.2. AI-Powered Converter (`core/agent.py`)

**Purpose**: The heart of the system - converts CIL to Promela using Google Gemini AI with intelligent error handling.

**Key Implementation Details**:

**CILToPromelaConverter Class**:
- **AI Model Integration**: Uses Google Gemini 2.0 Flash for code translation
- **Context-Aware Conversion**: Maintains global variables and function signatures across conversions
- **Iterative Refinement**: Automatically fixes errors through multiple AI iterations (max 5 by default)

**Core Conversion Process**:
```python
def convert(self, cil_code: str, context: Dict = None, fix_prompt: str = None) -> str:
    # 1. Extract global context (variables, functions)
    global_vars = self._extract_global_variables(cil_code)
    func_sigs = self._extract_function_signatures(cil_code)
    
    # 2. Build conversion prompt with context
    prompt = self._build_conversion_prompt(cil_code, global_vars, func_sigs)
    
    # 3. Call AI model for initial conversion
    promela_code = self.call_llm(prompt)
    
    # 4. Verify and iteratively fix errors
    is_valid, error_msg = self.verify_promela_code(promela_code)
    if not is_valid:
        promela_code = self._fix_iterations(promela_code, error_msg)
    
    return promela_code
```

**AI Prompt Engineering**:
- **Target-Specific Guidance**: Tailors prompts based on verification target (general, memory safety, concurrency)
- **Context Injection**: Includes global variables and function signatures in prompts
- **Error-Specific Fixes**: Generates targeted fix prompts based on SPIN error analysis

#### 3.2.3. Error Database & Learning System (`core/error_database.py`)

**Purpose**: Implements adaptive learning by storing error patterns, successful fixes, and fix prompts.

**Key Implementation Details**:

**Data Structures**:
```python
self.error_patterns = {}     # Categorized error patterns
self.fix_prompts = {}        # AI prompts for specific error types
self.successful_fixes = {}   # Proven successful fix examples
```

**Learning Mechanisms**:
- **Error Classification**: Automatically categorizes errors (syntax, semantic, type, channel, etc.)
- **Pattern Recognition**: Identifies recurring error patterns in similar code contexts
- **Fix Effectiveness Tracking**: Stores successful fixes for reuse in similar situations
- **Prompt Evolution**: Refines AI prompts based on fix success rates

**Error Types Handled**:
```python
error_types = [
    'redeclaration', 'undeclared_variable', 'syntax_error', 'type_error',
    'channel_error', 'assertion_violation', 'invalid_end_state', 'deadlock',
    'livelock', 'acceptance_cycle', 'ltl_violation', 'resource_exhaustion',
    'never_claim_error', 'array_index_error', 'divide_by_zero'
]
```

#### 3.2.4. Enhanced Error Handler (`core/agent.py` - ErrorHandler class)

**Purpose**: Provides comprehensive error analysis and automated fix suggestions.

**Key Implementation Details**:

**Error Analysis Pipeline**:
```python
def parse_spin_error(self, error_message: str) -> dict:
    # 1. Extract line numbers and error locations
    # 2. Classify error types using regex patterns
    # 3. Extract relevant code context
    # 4. Determine error severity and fix priority
    return error_info
```

**Automated Fix Generation**:
- **Context-Aware Fixes**: Considers surrounding code when generating fixes
- **Multi-Strategy Approach**: Tries different fix strategies based on error type
- **Learning Integration**: Uses historical fix data to improve suggestions

### 3.3. Web GUI Implementation (`gui/streamlit_app.py`)

**Purpose**: Provides an intuitive web interface for non-expert users.

**Key Features Implementation**:

**Real-Time Progress Tracking**:
```python
def on_status_update(message):
    st.session_state.conversion_log.append(f"[{datetime.now()}] {message}")
    
def on_error_found(error_type, message, error_info=None):
    st.session_state.errors_found.append({
        'type': error_type,
        'message': message,
        'info': error_info,
        'timestamp': datetime.now()
    })
```

**Interactive Features**:
- **File Upload**: Supports both C and CIL file uploads
- **Progress Visualization**: Step-by-step conversion progress with visual indicators
- **Error Analysis**: Detailed error reports with fix suggestions
- **Code Comparison**: Side-by-side diff view of original vs. fixed code
- **Download Options**: Export Promela code, conversion logs, and error reports

### 3.4. Verification Integration

**SPIN Model Checker Integration**:
```python
def verify_promela_code(self, promela_code: str) -> tuple[bool, str]:
    # 1. Create temporary Promela file
    # 2. Run SPIN syntax check
    # 3. Compile with gcc if syntax is valid
    # 4. Run basic verification
    # 5. Parse and categorize any errors
    return (is_valid, error_message)
```

**Verification Modes**:
- **Syntax Validation**: Basic Promela syntax checking
- **Compilation Check**: Ensures generated code compiles with SPIN
- **Property Verification**: Custom LTL property checking (future enhancement)

### 3.5. Advanced Features

#### 3.5.1. Batch Processing
- **Multi-File Support**: Processes entire directories of C files
- **Context Preservation**: Maintains global context across multiple files
- **Dependency Resolution**: Handles inter-file dependencies

#### 3.5.2. Adaptive Learning
- **Pattern Recognition**: ML-based identification of common error patterns
- **Fix Effectiveness Scoring**: Tracks success rates of different fix strategies
- **Prompt Optimization**: Automatically refines AI prompts based on outcomes

#### 3.5.3. Extensibility
- **Plugin Architecture**: Modular design allows easy addition of new verification targets
- **API Integration**: RESTful API for integration with other tools (future enhancement)
- **Custom Property Support**: Framework for user-defined verification properties

## 4. Key Technologies Used

*   **Python**: Core programming language for the application.
*   **Google Gemini API**: For AI-powered code translation and error correction.
*   **CIL (C Intermediate Language)**: As the standardized input format derived from C code.
*   **SPIN & Promela**: Target verification framework and language.
*   **Streamlit**: For building the interactive web-based GUI.
*   **Git & GitHub**: For version control and collaborative development.

## 5. System Requirements

*   **Operating System**:
    *   Windows 10/11 (WSL recommended for CIL and SPIN)
    *   Linux (Ubuntu 20.04+ or equivalent)
    *   macOS (10.15+ or equivalent, Homebrew recommended for dependencies)
*   **Python**: Version 3.8 or higher.
*   **Memory (RAM)**: Minimum 4GB, 8GB or more recommended for handling larger codebases and AI model operations.
*   **Storage**: At least 1GB of free disk space for the application, dependencies, and generated files.
*   **Internet Connection**: Required for accessing Google Gemini API for the AI-driven conversion.

## 6. Installation and Setup

Follow these steps to install and configure CToPromelaAgentic:

### 6.1. Obtain the Software
1.  Clone the repository or download the source code package.
    ```bash
    git clone <repository-url>
    ```
2.  Extract the archive (if downloaded as a zip) to a desired location on your system.
3.  Navigate to the project's root directory:
    ```bash
    cd CToPromelaAgentic
    ```

### 6.2. Python Environment Setup
1.  Ensure Python 3.8+ is installed. Verify with `python --version` and `pip --version`.
2.  Create and activate a Python virtual environment (recommended):
    ```bash
    # Create virtual environment
    python -m venv venv

    # Activate virtual environment
    # On Windows:
    venv\Scripts\activate
    # On Linux/macOS:
    source venv/bin/activate
    ```

### 6.3. Install Dependencies
Install the required Python packages using the provided requirements file:
```bash
pip install -r config/requirements.txt
```

### 6.4. Install CIL (C Intermediate Language)
CIL is a prerequisite for converting C code to its intermediate representation.

*   **Windows**:
    1.  Install Windows Subsystem for Linux (WSL).
    2.  Open a WSL terminal and run:
        ```bash
        sudo apt-get update
        sudo apt-get install -y cil
        ```
*   **Linux (Ubuntu/Debian)**:
    ```bash
    sudo apt-get update
    sudo apt-get install -y cil
    ```
*   **macOS**:
    Using Homebrew:
    ```bash
    brew install cil
    ```
    If `cil` is not available via Homebrew, you may need to compile it from source. Refer to the CIL documentation.

### 6.5. Install SPIN Model Checker
SPIN is required for verifying the generated Promela code.

*   **Windows**:
    1.  Download SPIN from its [official website](https://spinroot.com/spin/whatispin.html).
    2.  Extract the contents to a directory (e.g., `C:\spin`).
    3.  Add this directory to your system's PATH environment variable.
*   **Linux (Ubuntu/Debian)**:
    ```bash
    sudo apt-get update
    sudo apt-get install -y spin
    ```
*   **macOS**:
    Using Homebrew:
    ```bash
    brew install spin
    ```

### 6.6. Google API Key Setup
Access to Google's Gemini API is necessary for the AI conversion features.
1.  Visit [Google AI Studio](https://makersuite.google.com/app/apikey) or the Google Cloud Console.
2.  Sign in and create a new API key enabled for the Gemini models.
3.  Set the API key as an environment variable:
    ```bash
    # On Windows (Command Prompt):
    set GOOGLE_API_KEY=YOUR_API_KEY_HERE

    # On Linux/macOS (Bash/Zsh):
    export GOOGLE_API_KEY='YOUR_API_KEY_HERE'
    ```
    Alternatively, the application GUI will prompt for the API key if the environment variable is not set. You can also create a `.env` file in the project root (`CToPromelaAgentic/.env`) and add the line:
    `GOOGLE_API_KEY='YOUR_API_KEY_HERE'`
    The application will attempt to load the key from this file if the environment variable is not found.

## 7. Running the Application

CToPromelaAgentic can be run in GUI mode or via the command line for batch processing and testing.

### 7.1. GUI Mode (Recommended for Interactive Use)

*   **Windows**:
    1.  Ensure your virtual environment is activated.
    2.  Navigate to the project root directory in Command Prompt.
    3.  Execute the batch script:
        ```bash
        scripts\run_gui.bat
        ```
*   **Linux/macOS**:
    1.  Ensure your virtual environment is activated.
    2.  Navigate to the project root directory in your terminal.
    3.  Make the script executable (if not already):
        ```bash
        chmod +x scripts/run_gui.sh
        ```
    4.  Run the script:
        ```bash
        ./scripts/run_gui.sh
        ```
    This will launch the Streamlit web application, typically accessible at `http://localhost:8501` in your web browser.

### 7.2. Manual GUI Start (Alternative)
If the scripts encounter issues, or for development purposes:
```bash
# Ensure virtual environment is active
# (source venv/bin/activate or venv\Scripts\activate)

# Navigate to project root
cd path/to/CToPromelaAgentic

# Run Streamlit app directly
streamlit run gui/streamlit_app.py
```

### 7.3. Command Line Mode (for Testing and Batch Processing)
The `tests/test_unified.py` script serves as the command-line interface for some operations, primarily testing.
```bash
# Ensure virtual environment is active
cd path/to/CToPromelaAgentic

# Example: Run the entire test suite:
python tests/test_unified.py --all

# For direct CIL to Promela conversion via CLI (if supported by agent.py or a dedicated script):
# python core/agent.py --input path/to/your/input.cil --output path/to/your/output.pml
# (Note: Check specific CLI arguments for agent.py or other relevant scripts)
```
Use `python tests/test_unified.py --help` for test-specific command-line options. For direct conversion CLI, refer to the specific script's help or documentation.

## 8. Using the GUI

The Streamlit-based GUI provides an interactive way to use CToPromelaAgentic:

1.  **Initial Setup**:
    *   Launch the GUI as described above.
    *   If the `GOOGLE_API_KEY` is not set (as an environment variable or in a `.env` file), you will be prompted to enter it in the sidebar.
    *   Select the **Verification Target** (e.g., General, Memory Safety, Concurrency) to tailor the conversion and verification approach if this feature is implemented.

2.  **File Upload and Conversion Options**:
    *   Use the "Upload C File" or "Upload CIL File" button to select your input file. If a C file is uploaded, it will be preprocessed to CIL.
    *   Configure conversion parameters if available (e.g., AI Model choice, specific Promela generation flags).

3.  **Monitoring Conversion**:
    *   The GUI provides real-time updates on the conversion process.
    *   A status log displays messages about preprocessing, AI model interaction, code generation, and error detection.
    *   Progress bars and status indicators show the current stage.

4.  **Reviewing Results**:
    *   **Original Code Pane**: Displays the uploaded C or CIL code.
    *   **Generated Promela Pane**: Shows the converted Promela code. Differences from previous attempts or fixes can be highlighted.
    *   **Status Log Tab**: Detailed log of the entire conversion lifecycle.
    *   **Error Analysis Tab**: Lists any errors encountered during CIL parsing, conversion, or Promela generation. Provides context and potential causes.
    *   **Fix Iterations Tab**: If errors were found and fixes attempted, this tab shows the original erroneous Promela snippet and the AI-suggested corrected version.
    *   **Final Code Tab**: Presents the final, complete Promela code.

5.  **Saving Results**:
    *   Click the "Download Promela" button to save the generated Promela code to your local system.
    *   Options to download intermediate CIL code or conversion reports may also be available.

## 9. Practical Usage Examples & Common Use Cases

### 9.1. Basic C Program Conversion

**Example: Simple Banking System**

**Input C Code** (`bank_account.c`):
```c
#include <stdio.h>

typedef struct {
    int account_id;
    int balance;
} Account;

Account accounts[10];
int num_accounts = 0;

void deposit(int account_id, int amount) {
    for (int i = 0; i < num_accounts; i++) {
        if (accounts[i].account_id == account_id) {
            accounts[i].balance += amount;
            return;
        }
    }
}

int withdraw(int account_id, int amount) {
    for (int i = 0; i < num_accounts; i++) {
        if (accounts[i].account_id == account_id) {
            if (accounts[i].balance >= amount) {
                accounts[i].balance -= amount;
                return 1; // Success
            }
            return 0; // Insufficient funds
        }
    }
    return -1; // Account not found
}
```

**Generated Promela Code**:
```promela
/* CIL test file */

typedef Account {
    int account_id;
    int balance;
}

Account accounts[10];
int num_accounts = 0;

proctype deposit(int account_id; int amount) {
    int i = 0;
    do
    :: (i < num_accounts) ->
        if
        :: (accounts[i].account_id == account_id) ->
            accounts[i].balance = accounts[i].balance + amount;
            goto end_deposit
        :: else -> skip
        fi;
        i++
    :: else -> break
    od;
end_deposit:
}

proctype withdraw(int account_id; int amount; chan result) {
    int i = 0;
    do
    :: (i < num_accounts) ->
        if
        :: (accounts[i].account_id == account_id) ->
            if
            :: (accounts[i].balance >= amount) ->
                accounts[i].balance = accounts[i].balance - amount;
                result ! 1  // Success
            :: else ->
                result ! 0  // Insufficient funds
            fi;
            goto end_withdraw
        :: else -> skip
        fi;
        i++
    :: else ->
        result ! -1;  // Account not found
        break
    od;
end_withdraw:
}
```

### 9.2. Concurrency and Synchronization

**Example: Producer-Consumer Problem**

**Input C Code**:
```c
#include <pthread.h>
#include <semaphore.h>

#define BUFFER_SIZE 10

int buffer[BUFFER_SIZE];
int in = 0, out = 0;
sem_t empty, full, mutex;

void producer() {
    int item = 1;
    while (1) {
        sem_wait(&empty);
        sem_wait(&mutex);
        
        buffer[in] = item;
        in = (in + 1) % BUFFER_SIZE;
        
        sem_post(&mutex);
        sem_post(&full);
        item++;
    }
}

void consumer() {
    int item;
    while (1) {
        sem_wait(&full);
        sem_wait(&mutex);
        
        item = buffer[out];
        out = (out + 1) % BUFFER_SIZE;
        
        sem_post(&mutex);
        sem_post(&empty);
    }
}
```

**Generated Promela Code**:
```promela
#define BUFFER_SIZE 10

int buffer[BUFFER_SIZE];
int in = 0;
int out = 0;

chan empty = [BUFFER_SIZE] of {bit};
chan full = [0] of {bit};
chan mutex = [1] of {bit};

init {
    int i;
    // Initialize semaphores
    for (i : 0 .. BUFFER_SIZE-1) {
        empty ! 1
    };
    mutex ! 1;
    
    run producer();
    run consumer()
}

proctype producer() {
    int item = 1;
    do
    :: true ->
        empty ? _;
        mutex ? _;
        
        buffer[in] = item;
        in = (in + 1) % BUFFER_SIZE;
        
        mutex ! 1;
        full ! 1;
        item++
    od
}

proctype consumer() {
    int item;
    do
    :: true ->
        full ? _;
        mutex ? _;
        
        item = buffer[out];
        out = (out + 1) % BUFFER_SIZE;
        
        mutex ! 1;
        empty ! 1
    od
}
```

### 9.3. Memory Safety Verification

**Example: Array Bounds Checking**

**Input C Code**:
```c
#define MAX_SIZE 100

int array[MAX_SIZE];
int size = 0;

int safe_access(int index) {
    if (index >= 0 && index < size) {
        return array[index];
    }
    return -1; // Error code
}

void safe_insert(int index, int value) {
    if (index >= 0 && index <= size && size < MAX_SIZE) {
        for (int i = size; i > index; i--) {
            array[i] = array[i-1];
        }
        array[index] = value;
        size++;
    }
}
```

**Generated Promela Code with Assertions**:
```promela
#define MAX_SIZE 100

int array[MAX_SIZE];
int size = 0;

proctype safe_access(int index; chan result) {
    assert(index >= 0);  // Memory safety assertion
    assert(index < MAX_SIZE);  // Bounds checking
    
    if
    :: (index >= 0 && index < size) ->
        result ! array[index]
    :: else ->
        result ! -1
    fi
}

proctype safe_insert(int index; int value) {
    assert(index >= 0);  // Memory safety assertion
    assert(index <= size);  // Valid insertion point
    assert(size < MAX_SIZE);  // Buffer overflow prevention
    
    if
    :: (index >= 0 && index <= size && size < MAX_SIZE) ->
        int i = size;
        do
        :: (i > index) ->
            assert(i < MAX_SIZE && i-1 >= 0);  // Bounds checking
            array[i] = array[i-1];
            i--
        :: else -> break
        od;
        array[index] = value;
        size++
    :: else -> skip
    fi
}
```

### 9.4. Real-World Application: Network Protocol Verification

**Example: Simple TCP State Machine**

**Input C Code**:
```c
typedef enum {
    CLOSED, LISTEN, SYN_SENT, SYN_RECEIVED,
    ESTABLISHED, FIN_WAIT_1, FIN_WAIT_2,
    CLOSE_WAIT, CLOSING, LAST_ACK, TIME_WAIT
} tcp_state_t;

typedef struct {
    tcp_state_t state;
    int seq_num;
    int ack_num;
} tcp_connection_t;

void handle_syn(tcp_connection_t *conn) {
    switch (conn->state) {
        case CLOSED:
        case LISTEN:
            conn->state = SYN_RECEIVED;
            break;
        default:
            // Invalid transition
            break;
    }
}

void handle_ack(tcp_connection_t *conn) {
    switch (conn->state) {
        case SYN_RECEIVED:
            conn->state = ESTABLISHED;
            break;
        case FIN_WAIT_1:
            conn->state = FIN_WAIT_2;
            break;
        default:
            break;
    }
}
```

**Generated Promela Code for Protocol Verification**:
```promela
mtype = {CLOSED, LISTEN, SYN_SENT, SYN_RECEIVED,
         ESTABLISHED, FIN_WAIT_1, FIN_WAIT_2,
         CLOSE_WAIT, CLOSING, LAST_ACK, TIME_WAIT};

mtype = {SYN, ACK, FIN, RST};

typedef tcp_connection {
    mtype state;
    int seq_num;
    int ack_num;
}

tcp_connection conn;
chan events = [10] of {mtype};

proctype tcp_handler() {
    mtype event;
    
    conn.state = CLOSED;
    
    do
    :: events ? event ->
        if
        :: (event == SYN) ->
            if
            :: (conn.state == CLOSED || conn.state == LISTEN) ->
                conn.state = SYN_RECEIVED
            :: else -> skip
            fi
        :: (event == ACK) ->
            if
            :: (conn.state == SYN_RECEIVED) ->
                conn.state = ESTABLISHED
            :: (conn.state == FIN_WAIT_1) ->
                conn.state = FIN_WAIT_2
            :: else -> skip
            fi
        :: else -> skip
        fi
    od
}

// Property: Once established, connection should remain stable
ltl established_stability {
    [](conn.state == ESTABLISHED -> X(conn.state == ESTABLISHED || conn.state == FIN_WAIT_1))
}

init {
    run tcp_handler();
    
    // Simulate network events
    events ! SYN;
    events ! ACK;
}
```

### 9.5. Common Verification Properties

The generated Promela code can be used to verify various properties:

**Deadlock Freedom**:
```bash
spin -a generated_model.pml
gcc -o pan pan.c
./pan -D  # Check for deadlocks
```

**Custom LTL Properties**:
```promela
// Safety: No buffer overflow
ltl no_overflow { [](size <= MAX_SIZE) }

// Liveness: Producer eventually produces
ltl producer_progress { []<>(item > 0) }

// Mutual Exclusion: Only one process in critical section
ltl mutual_exclusion { [](!(proc1_in_cs && proc2_in_cs)) }
```

**Assertion Checking**:
```promela
// Runtime assertions for memory safety
assert(array_index >= 0 && array_index < ARRAY_SIZE);

// State invariants
assert(balance >= 0);  // Account balance cannot go negative

// Protocol correctness
assert(state != INVALID_STATE);
```

### 9.6. Performance and Scalability Considerations

**Model Size Optimization**:
- Use `#define` constants instead of variables where possible
- Minimize state space with appropriate data types
- Use channels efficiently (bounded vs unbounded)

**Verification Efficiency**:
```bash
# Use partial order reduction
spin -a -o3 model.pml

# Apply bitstate hashing for large models
./pan -DBITSTATE -w24

# Set memory limits
./pan -m1000000  # 1M states limit
```

## 10. Project Structure

The CToPromelaAgentic repository is organized as follows:

```
CToPromelaAgentic/
├── .git/                         # Git version control files (usually hidden).
├── .gitignore                    # Specifies intentionally untracked files for Git.
├── Readme.md                     # This documentation file.
│
├── archive/                      # For storing older versions or experimental code.
│
├── cil_test_files/               # Contains CIL files used specifically for testing the conversion process.
│   ├── account_extensions.cil
│   ├── account.cil
│   ├── bank_system.cil
│   └── transaction.cil
│
├── config/                       # Configuration files for the project.
│   └── requirements.txt          # Lists Python package dependencies.
│
├── core/                         # Contains the core logic of the application.
│   ├── agent.py                  # Main CILToPromelaConverter class, orchestrates AI interaction.
│   ├── CtoCILConvertor.py        # Handles conversion of C source to CIL using the CIL tool.
│   ├── error_database.py         # Manages storage and retrieval of error patterns and fixes.
│   └── diagnostic.py             # Utility for system diagnostics and checks.
│
├── data/                         # General data files, possibly including training data for error patterns or sample inputs.
│   ├── error_patterns.json       # JSON file for storing identified error patterns.
│   ├── fix_prompts.json          # JSON file for storing prompts used for AI-driven fixes.
│   └── test_cases.json           # JSON file describing various test cases.
│
├── docs/                         # Documentation files, research papers, or design documents.
│   ├── FULLTEXT01.pdf
│   ├── ieee97.pdf
│   └── mvs-spin-04.pdf
│
├── error_data/                   # Data related to errors and fixes, potentially redundant with `data/` or `logs/`.
│   ├── error_patterns.json
│   ├── fix_prompts.json
│   └── successful_fixes.json
│
├── gui/                          # Files related to the Streamlit Graphical User Interface.
│   ├── streamlit_app.py          # Main Streamlit application script.
│   └── streamlit_app_styles.css  # Custom CSS for styling the GUI.
│
├── logs/                         # Log files generated by the application during runtime.
│   ├── autofix_successes.json
│   └── error_patterns.json       # Logs of identified error patterns.
│
├── multi_output/                 # Directory for storing multiple output files from batch processing or varied configurations.
│
├── output/                       # Default directory for storing generated Promela files and other outputs.
│
├── results/                      # Directory for storing results from test runs or analyses.
│
├── scripts/                      # Utility scripts for running, testing, or managing the project.
│   ├── run_gui.bat               # Batch script to run the GUI on Windows.
│   └── run_gui.sh                # Shell script to run the GUI on Linux/macOS.
│
├── src/                          # Source code directory, possibly for C code to be converted or other utility modules.
│                                 # (If Python modules are primarily in `core/`, `src/` might be for other languages or components)
│
├── test_cases/                   # Contains various C or CIL files used as test inputs.
│   ├── all.cil
│   ├── array.cil
│   ├── channels.cil
│   ├── concurrency.cil
│   ├── loops.cil
│   ├── memory.cil
│   ├── README.md                 # Describes the test cases in this directory.
│   ├── simple.cil
│   ├── simplest.cil
│   └── structs.cil
│
├── tests/                        # Contains testing scripts and modules.
│   ├── test_unified.py           # Unified test runner for various test scenarios (CLI entry point).
│   ├── test_error_database.py    # Unit tests for the ErrorDatabase module.
│   └── test_case_manager.py      # Manages and processes test case results.
│
├── test_suite/                   # A more comprehensive suite for testing, potentially with complex scenarios.
│   ├── adaptive_learner.py
│   ├── advanced/
│   ├── basic/
│   ├── cil_files/
│   ├── converter.py
│   ├── error_data/
│   ├── error_database.py
│   ├── expected/
│   ├── expected_outputs/
│   ├── intermediate/
│   ├── README.md
│   ├── results/
│   ├── syntax_errors/
│   ├── test_cases/
│   ├── test_suite/
│   ├── test_suite_generator.py
│   └── verification/
│
└── venv/                         # Python virtual environment directory (typically added to .gitignore).
```

## 11. Potential Future Enhancements

*   **Expanded C Language Feature Support**: Improved handling of complex pointers, function pointers, and unions.
*   **Direct C++ to Promela Conversion**: Extending capabilities beyond CIL to directly parse and convert C++ features (e.g., classes, templates).
*   **Enhanced AI Model Fine-Tuning**: Fine-tuning the Gemini models on a larger corpus of C-to-Promela conversions for higher accuracy.
*   **Property Specification Assistance**: GUI tools to help users define LTL (Linear Temporal Logic) properties for verification in SPIN.
*   **Counterexample Visualization**: Integrating tools to visualize counterexamples found by SPIN back in the context of the original C code.
*   **Support for More Verification Backends**: Generating output for other model checkers or static analysis tools.
*   **Batch Processing from GUI**: Allowing users to upload multiple files or a project directory for batch conversion through the GUI.
*   **Integration with IDEs**: Developing plugins for popular IDEs like VS Code for seamless C code verification.
*   **More Granular Error Reporting**: Pinpointing exact locations in C code that lead to conversion issues or Promela verification failures.

## 12. How to Contribute

We welcome contributions to CToPromelaAgentic! Here are some ways you can help:

1.  **Reporting Bugs**: If you find a bug, please open an issue on the GitHub repository, providing detailed steps to reproduce it.
2.  **Suggesting Enhancements**: Have an idea for a new feature or improvement? Open an issue to discuss it.
3.  **Improving Documentation**: If you find parts of the documentation unclear or incomplete, feel free to suggest changes or submit a pull request.
4.  **Adding Test Cases**: Contribute new C or CIL test cases, especially those that cover edge cases or complex language features.
5.  **Submitting Code**:
    *   Fork the repository.
    *   Create a new branch for your feature or bug fix (`git checkout -b feature/your-feature-name`).
    *   Make your changes and commit them with clear messages.
    *   Push your changes to your fork (`git push origin feature/your-feature-name`).
    *   Open a pull request against the main repository.
    *   Ensure your code adheres to the project's coding style and includes relevant tests.

## 13. License

This project is intended for research and educational purposes. If you plan to use it for commercial applications, please review any licenses associated with the dependencies (CIL, SPIN, Google Gemini API) and the project itself.

(A specific open-source license like MIT, Apache 2.0, or GPL can be added here if applicable. For example:)

`This project is licensed under the MIT License - see the LICENSE.md file for details (if one exists).`

Please ensure compliance with the terms of use for any external services like the Google Gemini API.

---
*This README provides a comprehensive guide to CToPromelaAgentic. Last Updated: Corresponding to the latest structural and feature updates.* 
