#!/usr/bin/env python3
"""
Adaptive learner for CIL to Promela converter.
Analyzes test results and improves prompt templates based on identified patterns.
"""

import os
import sys
import json
import re
import argparse
import numpy as np
from typing import Dict, List, Any, Tuple, Optional
from collections import Counter, defaultdict

# Add parent directory to path to import the converter
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from CtoPromellaWithRun import CILToPromelaConverter

# Configuration
RESULT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
PROMPT_TEMPLATE_DIR = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 
    "prompt_templates"
)

class AdaptiveLearner:
    """Adaptive learner for CIL to Promela converter."""
    
    def __init__(self, results_file: str):
        """Initialize adaptive learner.
        
        Args:
            results_file: Path to the test results file
        """
        self.results_file = results_file
        
        # Load test results
        with open(results_file, 'r') as f:
            self.results = json.load(f)
        
        # Create prompt template directory if it doesn't exist
        os.makedirs(PROMPT_TEMPLATE_DIR, exist_ok=True)
        
        # Load current prompt templates
        self.converter = CILToPromelaConverter(
            api_key="dummy",  # Not used for template extraction
            test_mode=True
        )
        self.current_conversion_prompt = self.converter.conversion_prompt
        self.current_error_fix_prompt = self.converter.error_fix_prompt
        
        # Initialize error pattern analysis
        self.error_patterns = defaultdict(int)
        self.syntax_fixes = defaultdict(list)
        self.successful_fixes = []
        self.failed_fixes = []
        
        # Define error pattern regexes
        self.error_patterns = {
            "syntax_error": r'syntax error[^a-zA-Z]*([a-zA-Z][^\n]*)',
            "undeclared_variable": r'undeclared variable: ([^\s,;]+)',
            "redeclaration": r'redeclaration of \'([^\s\']+)\'',
            "unexpected_token": r'expected ([^,;\n]+), saw ([^,;\n]+)'
        }
    
    def analyze_results(self) -> Dict[str, Any]:
        """Analyze test results to identify patterns.
        
        Returns:
            Dictionary with analysis results
        """
        print("Analyzing test results...")
        
        analysis = {
            "total_tests": self.results["summary"]["total"],
            "success_rate": self.results["summary"]["passed"] / self.results["summary"]["total"],
            "error_patterns": {},
            "fix_patterns": {},
            "prompt_improvement_suggestions": []
        }
        
        # Extract error patterns
        for test in self.results["tests"]:
            # Skip successful tests
            if test["success"]:
                if test["iterations"] > 0:
                    self.successful_fixes.append({
                        "test": test["name"],
                        "category": test["category"],
                        "iterations": test["iterations"],
                        "errors": test["errors"],
                        "promela_code": test["promela_code"]
                    })
                continue
            
            self.failed_fixes.append({
                "test": test["name"],
                "category": test["category"],
                "iterations": test["iterations"],
                "errors": test["errors"],
                "promela_code": test["promela_code"],
                "failure_reason": test["failure_reason"]
            })
            
            # Extract error patterns
            for error in test.get("errors", []):
                error_msg = error.get("message", "")
                self._extract_error_patterns(error_msg)
        
        # Count error patterns
        analysis["error_patterns"] = dict(self.error_patterns)
        
        # Identify common patterns
        if self.error_patterns:
            top_errors = sorted(
                self.error_patterns.items(), 
                key=lambda x: x[1], 
                reverse=True
            )[:10]
            
            print("\nTop 10 Error Patterns:")
            for pattern, count in top_errors:
                print(f"- {pattern}: {count} occurrences")
                
            analysis["top_errors"] = top_errors
        
        # Analyze syntax fixes
        if self.successful_fixes:
            fix_patterns = self._analyze_successful_fixes()
            analysis["fix_patterns"] = fix_patterns
            
            print("\nSuccessful Fix Patterns:")
            for pattern, count in fix_patterns.items():
                print(f"- {pattern}: {count} occurrences")
        
        # Generate prompt improvement suggestions
        suggestions = self._generate_improvement_suggestions(analysis)
        analysis["prompt_improvement_suggestions"] = suggestions
        
        return analysis
    
    def _extract_error_patterns(self, error_msg: str) -> None:
        """Extract error patterns from error messages.
        
        Args:
            error_msg: Error message from SPIN
        """
        error_msg_lower = error_msg.lower()
        
        # Extract error types using regex patterns
        for error_type, pattern in self.error_patterns.items():
            match = re.search(pattern, error_msg_lower)
            if match:
                if error_type == "unexpected_token":
                    pattern_key = f"{error_type}:expected_{match.group(1)}_saw_{match.group(2)}"
                else:
                    pattern_key = f"{error_type}:{match.group(1).strip()}"
                self.error_patterns[pattern_key] += 1
                return
        
        # Generic error pattern catch-all
        first_line = error_msg.split('\n')[0].strip()
        if first_line:
            # Generalize the error pattern
            pattern = re.sub(r'line\s+\d+', 'line_X', first_line.lower())
            pattern = re.sub(r'\b\w+\.\w+\b', 'file.ext', pattern)
            self.error_patterns[pattern] += 1
    
    def _analyze_successful_fixes(self) -> Dict[str, int]:
        """Analyze successful fixes to identify patterns.
        
        Returns:
            Dictionary with fix patterns and counts
        """
        fix_patterns = defaultdict(int)
        
        for fix in self.successful_fixes:
            # Extract error and fixed code
            initial_errors = fix["errors"][0]["message"] if fix["errors"] else ""
            promela_code = fix["promela_code"]
            
            # Define fix patterns and their conditions
            fix_pattern_conditions = {
                "fix_return_values": lambda e, c: "saw 'data typename'" in e,
                "add_missing_semicolons": lambda e, c: "missing semicolon" in e or "expected ';'" in e,
                "fix_if_structure": lambda e, c: "saw 'keyword: if'" in e,
                "fix_loop_structure": lambda e, c: "saw 'keyword: do'" in e,
                "rename_variables": lambda e, c: "redeclaration" in e,
                "add_variable_declaration": lambda e, c: "undeclared variable" in e,
                "appropriate_type_selection": lambda e, c: "int" in c and "byte" in c,
                "use_atomic_sections": lambda e, c: "atomic {" in c,
                "use_active_proctype": lambda e, c: "active proctype" in c,
                "add_end_labels": lambda e, c: "end: skip;" in c,
                "flatten_oop_structure": lambda e, c: any(x in e for x in ["class", "method", "return"]) and "[" in c
            }
            
            # Apply fix patterns
            for pattern, condition in fix_pattern_conditions.items():
                if condition(initial_errors, promela_code):
                    fix_patterns[pattern] += 1
        
        return dict(fix_patterns)
    
    def _generate_improvement_suggestions(self, analysis: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Generate prompt improvement suggestions based on analysis.
        
        Args:
            analysis: Analysis results
            
        Returns:
            List of improvement suggestions
        """
        suggestions = []
        
        # Generate suggestions based on error patterns
        if "top_errors" in analysis:
            for pattern, count in analysis["top_errors"]:
                suggestion = {
                    "type": "error_pattern",
                    "pattern": pattern,
                    "count": count,
                    "priority": "high" if count > 5 else "medium",
                    "description": f"Add specific handling for {pattern} errors"
                }
                suggestions.append(suggestion)
        
        # Generate suggestions based on fix patterns
        if "fix_patterns" in analysis:
            for pattern, count in analysis["fix_patterns"].items():
                if count > 2:  # Only suggest improvements for frequently successful fixes
                    suggestion = {
                        "type": "fix_pattern",
                        "pattern": pattern,
                        "count": count,
                        "priority": "high" if count > 5 else "medium",
                        "description": f"Enhance handling of {pattern} fixes"
                    }
                    suggestions.append(suggestion)
        
        return suggestions
    
    def generate_improved_prompts(self, analysis: Dict[str, Any]) -> Tuple[str, str]:
        """Generate improved prompt templates based on analysis.
        
        Args:
            analysis: Analysis results
            
        Returns:
            Tuple of (conversion_prompt, error_fix_prompt)
        """
        # Start with current prompts
        conversion_prompt = self.current_conversion_prompt
        error_fix_prompt = self.current_error_fix_prompt
        
        # Add error pattern handling
        if "top_errors" in analysis:
            error_handling = "\nCommon error patterns to handle:\n"
            for pattern, count in analysis["top_errors"]:
                error_handling += f"- {pattern}: {count} occurrences\n"
            conversion_prompt += error_handling
        
        # Add fix pattern handling
        if "fix_patterns" in analysis:
            fix_handling = "\nSuccessful fix patterns to apply:\n"
            for pattern, count in analysis["fix_patterns"].items():
                if count > 2:  # Only include frequently successful fixes
                    fix_handling += f"- {pattern}: {count} successes\n"
            error_fix_prompt += fix_handling
        
        return conversion_prompt, error_fix_prompt

def main():
    """Main function."""
    parser = argparse.ArgumentParser(description="Adaptive learner for CIL to Promela converter")
    parser.add_argument("results_file", help="Path to test results file")
    args = parser.parse_args()
    
    learner = AdaptiveLearner(args.results_file)
    analysis = learner.analyze_results()
    
    # Generate improved prompts
    conversion_prompt, error_fix_prompt = learner.generate_improved_prompts(analysis)
    
    # Save improved prompts
    os.makedirs(PROMPT_TEMPLATE_DIR, exist_ok=True)
    
    with open(os.path.join(PROMPT_TEMPLATE_DIR, "conversion_prompt.txt"), 'w') as f:
        f.write(conversion_prompt)
    
    with open(os.path.join(PROMPT_TEMPLATE_DIR, "error_fix_prompt.txt"), 'w') as f:
        f.write(error_fix_prompt)
    
    print("\nImproved prompts saved to prompt_templates directory")

if __name__ == "__main__":
    main() 