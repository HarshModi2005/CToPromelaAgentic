#!/usr/bin/env python3
"""
CIL to Promela converter.
Converts C Intermediate Language (CIL) code to Promela for verification.
"""

import os
import re
import json
import logging
import subprocess
import datetime
import tempfile
from typing import List, Tuple, Dict, Any, Optional

# You'll need to install these dependencies:
# pip install google-generativeai
import google.generativeai as genai

# Set up logging
logging.basicConfig(level=logging.INFO, 
                   format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class CILToPromelaConverter:
    def __init__(self, api_key: str, model: str = "gemini-2.0-flash", spin_path: str = "spin"):
        self.api_key = api_key
        self.spin_path = spin_path
        self.logger = logging.getLogger('CILToPromelaConverter')
        
        # Initialize Gemini API
        genai.configure(api_key=api_key)
        self.model = genai.GenerativeModel(model)
    
    def convert(self, cil_code: str, fix_prompt: str = None) -> str:
        """Convert CIL code to Promela with optional fix prompt."""
        try:
            # Initial conversion
            promela_code = self._convert_cil_to_promela(cil_code)
            
            # Apply fixes if provided
            if fix_prompt:
                promela_code = self._apply_fix(promela_code, fix_prompt)
            
            # Post-process the code
            promela_code = self._post_process_promela_code(promela_code)
            
            return promela_code
            
        except Exception as e:
            self.logger.error(f"Error during conversion: {str(e)}")
            raise
    
    def _convert_cil_to_promela(self, cil_code: str) -> str:
        """Convert CIL code to Promela."""
        # Construct the prompt
        prompt = f"""
        Convert the following C Intermediate Language (CIL) code to Promela.
        Follow these rules:
        1. Convert all data types to Promela types (bit, bool, byte, short, int)
        2. Convert functions to inline or proctype as appropriate
        3. Handle printf statements correctly
        4. Convert loops to do...od format
        5. Convert arrays and structs to Promela format
        6. Handle channel operations correctly
        7. Add proper process declarations
        8. Ensure atomic operations are handled correctly
        
        CIL Code:
        {cil_code}
        """
        
        # Call LLM
        response = self.call_llm(prompt)
        
        # Extract code from response
        promela_code = self._extract_code_from_response(response)
        
        # Apply initial fixes
        promela_code = self._fix_data_types(promela_code)
        promela_code = self._fix_function_declarations(promela_code)
        promela_code = self._fix_control_structures(promela_code)
        promela_code = self._fix_printf_format(promela_code)
        promela_code = self._fix_process_declarations(promela_code)
        promela_code = self._fix_channel_declarations(promela_code)
        promela_code = self._fix_atomic_blocks(promela_code)
        promela_code = self._fix_boolean_declarations(promela_code)
        promela_code = self._fix_array_declarations(promela_code)
        promela_code = self._handle_variable_declarations(promela_code)
        
        # Apply new fixes
        promela_code = self._fix_struct_declarations(promela_code)
        promela_code = self._fix_nested_loops(promela_code)
        promela_code = self._fix_complex_conditionals(promela_code)
        promela_code = self._fix_memory_management(promela_code)
        promela_code = self._fix_process_synchronization(promela_code)
        promela_code = self._fix_channel_operations(promela_code)
        promela_code = self._fix_deadlock_prevention(promela_code)
        promela_code = self._fix_livelock_prevention(promela_code)
        promela_code = self._fix_race_conditions(promela_code)
        
        return promela_code
    
    def _apply_fix(self, promela_code: str, fix_prompt: str) -> str:
        """Apply a fix to the Promela code based on the fix prompt."""
        # Construct the fix prompt
        prompt = f"""
        Fix the following Promela code according to this guidance:
        {fix_prompt}
        
        Current code:
        {promela_code}
        """
        
        # Call LLM
        response = self.call_llm(prompt)
        
        # Extract fixed code
        fixed_code = self._extract_code_from_response(response)
        
        # Apply post-processing
        fixed_code = self._post_process_promela_code(fixed_code)
        
        return fixed_code
    
    def _fix_data_types(self, code: str) -> str:
        """Fix C data types to match Promela syntax."""
        # Type mapping
        type_map = {
            r'\bint\b(?!\s*\w+\s*\[)': 'byte',  # int to byte, but not for array declarations
            r'\blong\b': 'int',
            r'\bshort\b': 'byte',
            r'\bchar\b': 'byte',
            r'\bunsigned\s+int\b': 'byte',
            r'\bunsigned\s+char\b': 'byte',
            r'\bfloat\b': 'int',  # Promela doesn't support floating point
            r'\bdouble\b': 'int',  # Promela doesn't support floating point
            r'\bvoid\b': '',  # Remove void type
            r'\bsize_t\b': 'byte',  # Common type mappings
            r'\buint8_t\b': 'byte',
            r'\buint16_t\b': 'byte',
            r'\buint32_t\b': 'int',
            r'\buint64_t\b': 'int',
            r'\bint8_t\b': 'byte',
            r'\bint16_t\b': 'byte',
            r'\bint32_t\b': 'int',
            r'\bint64_t\b': 'int',
            r'\bbool\b': 'bool',
            r'\b_Bool\b': 'bool',
            r'\bboolean\b': 'bool'
        }
        
        # Apply type conversions
        for pattern, replacement in type_map.items():
            code = re.sub(pattern, replacement, code)
        
        # Handle arrays
        code = re.sub(
            r'(\w+)\s+(\w+)\s*\[(\d+)\]',
            r'byte \2[\3]',  # Convert all arrays to byte arrays
            code
        )
        
        # Handle pointers
        code = re.sub(
            r'(\w+)\s*\*\s*(\w+)',
            r'byte \2',  # Convert pointers to byte variables
            code
        )
        
        # Handle function pointers
        code = re.sub(
            r'(\w+)\s*\(\s*\*\s*(\w+)\s*\)\s*\(([^)]*)\)',
            r'inline \2(\3)',
            code
        )
        
        # Clean up C-style declarations
        code = re.sub(r'typedef\s+[^;]+;', '', code)  # Remove typedefs
        code = re.sub(r'#include\s+[<"][^>"]+[>"]', '', code)  # Remove includes
        code = re.sub(r'#define\s+\w+\s+[^\n]+', '', code)  # Remove defines
        
        return code
    
    def _fix_control_structures(self, code: str) -> str:
        """Fix C control structures to match Promela syntax."""
        # Fix if statements
        code = re.sub(
            r'if\s*\(([^)]+)\)\s*{([^}]+)}(\s*else\s*{([^}]+)})?',
            lambda m: f"if\n:: {m.group(1)} -> {m.group(2)}\n" + 
                     (f":: else -> {m.group(4)}\n" if m.group(3) else "") + "fi",
            code
        )
        
        # Fix while loops
        code = re.sub(
            r'while\s*\(([^)]+)\)\s*{([^}]+)}',
            lambda m: f"do\n:: {m.group(1)} -> {m.group(2)}\n:: else -> break\nod",
            code
        )
        
        # Fix for loops
        code = re.sub(
            r'for\s*\(([^;]+);\s*([^;]+);\s*([^)]+)\)\s*{([^}]+)}',
            lambda m: f"{m.group(1)};\ndo\n:: {m.group(2)} -> {m.group(4)}\n  {m.group(3)};\n:: else -> break\nod",
            code
        )
        
        return code
    
    def _fix_printf_format(self, code: str) -> str:
        """Fix printf format strings in Promela code."""
        def fix_printf(match):
            format_str = match.group(1)
            args = match.group(2)
            
            if not args:
                return f'printf("{format_str}")'
            
            # Split format string and arguments
            parts = []
            current_pos = 0
            args_list = [arg.strip() for arg in args.split(',')]
            arg_index = 0
            
            # Find all format specifiers
            format_specs = re.finditer(r'%[diufFeEgGxXoscpaA]', format_str)
            for spec in format_specs:
                # Add text before format specifier
                if spec.start() > current_pos:
                    text = format_str[current_pos:spec.start()]
                    if text:
                        parts.append(f'printf("{text}")')
                
                # Add format specifier with argument
                if arg_index < len(args_list):
                    parts.append(f'printf("{spec.group()}", {args_list[arg_index]})')
                    arg_index += 1
                
                current_pos = spec.end()
            
            # Add remaining text
            if current_pos < len(format_str):
                text = format_str[current_pos:]
                if text:
                    parts.append(f'printf("{text}")')
            
            return ';\n'.join(parts)
        
        # Find and fix printf statements
        code = re.sub(
            r'printf\s*\(\s*"([^"]+)"\s*(?:,\s*([^)]+))?\s*\)',
            fix_printf,
            code
        )
        
        return code
    
    def _fix_process_declarations(self, code: str) -> str:
        """Fix process declarations to match Promela syntax."""
        # Convert void functions to proctypes
        code = re.sub(
            r'void\s+(\w+)\s*\(\s*(?:void)?\s*\)',
            r'proctype \1()',
            code
        )
        
        # Convert main to init
        code = re.sub(
            r'void\s+main\s*\(\s*(?:void)?\s*\)',
            'init',
            code
        )
        
        return code
    
    def _fix_channel_declarations(self, code: str) -> str:
        """Fix channel declarations to match Promela syntax."""
        # Fix channel declarations
        code = re.sub(
            r'chan\s+(\w+)\s*=\s*\[\s*(\d+)\s*\]\s*of\s*{([^}]+)}',
            r'chan \1 = [\2] of {\3}',
            code
        )
        
        return code
    
    def _fix_atomic_blocks(self, code: str) -> str:
        """Fix atomic blocks to match Promela syntax."""
        # Convert atomic blocks to d_step
        code = re.sub(
            r'atomic\s*{([^}]+)}',
            r'd_step {\1}',
            code
        )
        
        return code
    
    def _fix_boolean_declarations(self, code: str) -> str:
        """Fix boolean declarations to match Promela syntax."""
        # Add mtype declaration for boolean values if needed
        if 'bool' in code and not 'mtype = {true, false}' in code:
            code = 'mtype = {true, false};\n' + code
        
        # Fix boolean declarations
        code = re.sub(
            r'(?:bool|_Bool)\s+(\w+)',
            r'bool \1',
            code
        )
        
        return code
    
    def _fix_array_declarations(self, code: str) -> str:
        """Fix array declarations to match Promela syntax."""
        # Fix array declarations
        code = re.sub(
            r'(\w+)\s+(\w+)\s*\[\s*(\d+)\s*\]',
            r'\1 \2[\3]',
            code
        )
        
        return code
    
    def _handle_variable_declarations(self, code: str) -> str:
        """Handle variable declarations to match Promela syntax."""
        # Move all declarations to the top
        declarations = []
        code_lines = []
        
        for line in code.split('\n'):
            if re.match(r'^\s*(byte|bool|int|short|mtype)\s+\w+', line):
                declarations.append(line)
            else:
                code_lines.append(line)
        
        return '\n'.join(declarations + code_lines)
    
    def _post_process_promela_code(self, code: str) -> str:
        """Post-process Promela code to fix common issues."""
        # Fix printf statements
        code = re.sub(r'printf\s*\(\s*"([^"]*)"(?:\s*,\s*([^)]+))?\s*\)\s*;?',
                     lambda m: f'printf("{m.group(1)}"{", " + m.group(2) if m.group(2) else ""})',
                     code)
        
        # Fix semicolons
        code = re.sub(r';\s*\n\s*}', r'\n}', code)
        code = re.sub(r';\s*\n\s*od', r'\nod', code)
        code = re.sub(r';\s*\n\s*fi', r'\nfi', code)
        
        return code
    
    def call_llm(self, prompt: str) -> str:
        """Call the LLM with retry logic."""
        try:
            response = self.model.generate_content(prompt)
            return response.text
        except Exception as e:
            self.logger.error(f"Error calling LLM: {str(e)}")
            raise
    
    def _extract_code_from_response(self, response: str) -> str:
        """Extract code from LLM response."""
        # Look for code blocks
        code_blocks = re.findall(r'```(?:promela)?\n(.*?)```', response, re.DOTALL)
        if code_blocks:
            return code_blocks[0].strip()
        
        # If no code blocks, try to extract the code directly
        lines = response.split('\n')
        code_lines = []
        in_code = False
        
        for line in lines:
            if line.strip().startswith('/*') or line.strip().startswith('//'):
                continue
            if line.strip() and not line.startswith(('Here', 'This', 'The', 'Note', 'Remember')):
                code_lines.append(line)
        
        return '\n'.join(code_lines).strip()

    def _fix_function_declarations(self, code: str) -> str:
        """Fix function declarations to match Promela syntax."""
        # Convert C functions to inline functions
        def convert_function(match):
            return_type = match.group(1)
            func_name = match.group(2)
            params = match.group(3)
            
            # Parse parameters
            param_list = [p.strip() for p in params.split(',') if p.strip()]
            
            # Add result parameter for non-void functions
            if return_type != 'void':
                param_list.append('result')
            
            # Convert parameter types to Promela types
            param_list = [f'byte {p.split()[-1]}' for p in param_list]
            
            # Create inline function declaration
            return f'inline {func_name}({", ".join(param_list)})'
        
        # Convert function declarations
        code = re.sub(
            r'(?:int|void|char|float|double)\s+(\w+)\s*\(\s*([^)]*)\s*\)',
            convert_function,
            code
        )
        
        # Convert return statements to assignments
        code = re.sub(
            r'return\s+([^;]+);',
            lambda m: f'result = {m.group(1)};',
            code
        )
        
        return code

    def _fix_struct_declarations(self, code: str) -> str:
        """Fix struct declarations and handle pointer arithmetic."""
        # Handle struct declarations
        def convert_struct(match):
            struct_name = match.group(1)
            fields = match.group(2)
            
            # Parse fields
            field_list = []
            for field in fields.split(';'):
                if not field.strip():
                    continue
                field = field.strip()
                if ':' in field:  # Handle bit fields
                    name, bits = field.split(':')
                    field_list.append(f"byte {name.strip()}:{bits.strip()}")
                else:
                    # Convert C types to Promela types
                    field = re.sub(r'\bint\b', 'byte', field)
                    field = re.sub(r'\blong\b', 'int', field)
                    field = re.sub(r'\bshort\b', 'byte', field)
                    field = re.sub(r'\bchar\b', 'byte', field)
                    field_list.append(field)
            
            # Create Promela struct declaration
            return f"typedef {struct_name} {{\n  " + "\n  ".join(field_list) + "\n}}"
        
        # Convert struct declarations
        code = re.sub(
            r'struct\s+(\w+)\s*{([^}]+)}',
            convert_struct,
            code
        )
        
        # Handle pointer arithmetic
        def convert_pointer_arithmetic(match):
            ptr = match.group(1)
            offset = match.group(2)
            return f"{ptr}[{offset}]"
        
        # Convert pointer arithmetic to array access
        code = re.sub(
            r'(\w+)\s*\+\s*(\d+)',
            convert_pointer_arithmetic,
            code
        )
        
        return code

    def _fix_nested_loops(self, code: str) -> str:
        """Fix nested loops to match Promela syntax."""
        def convert_nested_loop(match):
            outer_cond = match.group(1)
            inner_cond = match.group(2)
            outer_body = match.group(3)
            inner_body = match.group(4)
            
            # Convert to Promela nested do...od
            return f"""do
:: {outer_cond} ->
  do
  :: {inner_cond} ->
    {inner_body}
  :: else -> break
  od;
  {outer_body}
:: else -> break
od"""
        
        # Convert nested while loops
        code = re.sub(
            r'while\s*\(([^)]+)\)\s*{([^}]*?)while\s*\(([^)]+)\)\s*{([^}]+)}([^}]*?)}',
            convert_nested_loop,
            code
        )
        
        return code

    def _fix_complex_conditionals(self, code: str) -> str:
        """Fix complex conditionals to match Promela syntax."""
        def convert_complex_conditional(match):
            condition = match.group(1)
            true_branch = match.group(2)
            false_branch = match.group(3) if match.group(3) else ""
            
            # Split complex conditions
            conditions = re.split(r'\s*(?:&&|\|\|)\s*', condition)
            
            # Convert to Promela if...fi
            result = "if\n"
            for cond in conditions:
                result += f":: {cond} -> {true_branch}\n"
            if false_branch:
                result += f":: else -> {false_branch}\n"
            result += "fi"
            
            return result
        
        # Convert complex if statements
        code = re.sub(
            r'if\s*\(([^)]+)\)\s*{([^}]+)}(?:\s*else\s*{([^}]+)})?',
            convert_complex_conditional,
            code
        )
        
        return code

    def _fix_memory_management(self, code: str) -> str:
        """Fix memory management operations."""
        # Convert malloc to array allocation
        code = re.sub(
            r'malloc\s*\(\s*sizeof\s*\(\s*(\w+)\s*\)\s*\*\s*(\w+)\s*\)',
            r'byte \2[\1]',
            code
        )
        
        # Convert free to array deallocation
        code = re.sub(
            r'free\s*\(\s*(\w+)\s*\)',
            r'/* free(\1) */',
            code
        )
        
        return code

    def _fix_process_synchronization(self, code: str) -> str:
        """Fix process synchronization primitives."""
        # Convert mutex to Promela channels
        code = re.sub(
            r'pthread_mutex_t\s+(\w+)',
            r'chan \1 = [1] of {byte}',
            code
        )
        
        # Convert mutex operations
        code = re.sub(
            r'pthread_mutex_lock\s*\(\s*&\s*(\w+)\s*\)',
            r'\1!1',
            code
        )
        code = re.sub(
            r'pthread_mutex_unlock\s*\(\s*&\s*(\w+)\s*\)',
            r'\1?1',
            code
        )
        
        return code

    def _fix_channel_operations(self, code: str) -> str:
        """Fix channel operations."""
        # Convert channel declarations
        code = re.sub(
            r'chan\s+(\w+)\s*=\s*\[\s*(\d+)\s*\]\s*of\s*{([^}]+)}',
            r'chan \1 = [\2] of {\3}',
            code
        )
        
        # Convert channel operations
        code = re.sub(
            r'(\w+)\s*!\s*([^;]+)',
            r'\1!\2',
            code
        )
        code = re.sub(
            r'(\w+)\s*\?\s*([^;]+)',
            r'\1?\2',
            code
        )
        
        return code

    def _add_progress_label(self, code: str) -> str:
        """Add progress label to process declarations."""
        return re.sub(
            r'proctype\s+(\w+)',
            r'proctype \1\nprogress: skip;',
            code
        )

    def _fix_deadlock_prevention(self, code: str) -> str:
        """Add deadlock prevention mechanisms."""
        # Add timeout mechanism
        code = re.sub(
            r'do\s*::\s*([^:]+):',
            r'do\n:: timeout -> break\n:: \1:',
            code
        )
        
        # Add progress label
        code = self._add_progress_label(code)
        
        return code

    def _fix_livelock_prevention(self, code: str) -> str:
        """Add livelock prevention mechanisms."""
        # Add fairness constraints
        code = re.sub(
            r'do\s*::\s*([^:]+):',
            r'do\n:: (true) -> break\n:: \1:',
            code
        )
        
        # Add progress label
        code = self._add_progress_label(code)
        
        return code

    def _fix_race_conditions(self, code: str) -> str:
        """Fix race conditions."""
        # Add atomic blocks for critical sections
        code = re.sub(
            r'(\w+)\s*=\s*(\w+)\s*\+\s*1',
            r'atomic { \1 = \2 + 1 }',
            code
        )
        
        # Add mutex protection
        code = re.sub(
            r'(\w+)\s*=\s*(\w+)',
            r'atomic { \1 = \2 }',
            code
        )
        
        return code

def main():
    """Main function."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Convert CIL code to Promela")
    parser.add_argument("--api-key", help="API key for the model")
    parser.add_argument("--model", default="gemini-2.0-flash", help="Model to use")
    parser.add_argument("--spin-path", default="spin", help="Path to Spin executable")
    parser.add_argument("input_file", help="Input CIL file")
    parser.add_argument("--output-file", help="Output Promela file")
    
    args = parser.parse_args()
    
    # Read input file
    with open(args.input_file, 'r') as f:
        cil_code = f.read()
    
    # Convert code
    converter = CILToPromelaConverter(args.api_key, args.model, args.spin_path)
    promela_code = converter.convert(cil_code)
    
    # Write output
    if args.output_file:
        with open(args.output_file, 'w') as f:
            f.write(promela_code)
    else:
        print(promela_code)

if __name__ == "__main__":
    main() 