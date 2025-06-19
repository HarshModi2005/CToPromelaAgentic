#!/usr/bin/env python3
"""
Error database for CIL to Promela converter.
Stores and manages error patterns and their fixes.
"""

import json
import os
from typing import Dict, List, Any, Optional
from datetime import datetime

class ErrorDatabase:
    def __init__(self, db_path: str = "error_data"):
        self.db_path = db_path
        self.error_patterns: Dict[str, List[Dict[str, Any]]] = {}
        self.fix_patterns: Dict[str, List[Dict[str, Any]]] = {}
        self.successful_fixes: Dict[str, int] = {}
        
        # Create database directory if it doesn't exist
        os.makedirs(db_path, exist_ok=True)
        
        # Load existing data if available
        self._load_data()
        
        # Initialize error patterns
        self._init_error_patterns()
    
    def _init_error_patterns(self):
        """Initialize all error patterns and their fixes."""
        patterns = {
            # Basic syntax errors
            "printf_format": {
                "pattern": "saw 'function-name: printf'",
                "fix_description": "Convert C-style printf with format specifiers to Promela printf statements",
                "example": """
                // C code:
                printf("Value: %d\\n", x);
                
                // Promela code:
                printf("Value: %d\\n", x)
                """
            },
            "data_type": {
                "pattern": "saw 'data typename'",
                "fix_description": "Convert C data types to Promela types",
                "example": """
                // C code:
                int x;
                byte y;
                
                // Promela code:
                int x;
                byte y;
                """
            },
            "channel_syntax": {
                "pattern": "saw 'keyword: of'",
                "fix_description": "Fix channel declaration syntax",
                "example": """
                // C code:
                chan ch = [2] of {int};
                
                // Promela code:
                chan ch = [2] of {int};
                """
            },
            "process_declaration": {
                "pattern": "saw 'keyword: proctype'",
                "fix_description": "Fix process declaration syntax",
                "example": """
                // C code:
                void process() { ... }
                
                // Promela code:
                proctype process() { ... }
                """
            },
            "function_declaration": {
                "pattern": "saw 'inline name'",
                "fix_description": "Convert C functions to Promela inline functions",
                "example": """
                // C code:
                int func(int x) { return x * 2; }
                
                // Promela code:
                inline func(x, result) {
                    result = x * 2
                }
                """
            },
            # Complex feature errors
            "struct_declaration_error": {
                "pattern": "Invalid struct declaration",
                "fix_description": "Convert struct declarations to Promela typedef",
                "example": "typedef {struct_name} {{\n  {fields}\n}}"
            },
            "pointer_arithmetic_error": {
                "pattern": "Invalid pointer arithmetic",
                "fix_description": "Convert pointer arithmetic to array access",
                "example": "{array}[{index}]"
            },
            "nested_loop_error": {
                "pattern": "Invalid nested loop structure",
                "fix_description": "Convert nested loops to Promela do...od format",
                "example": "do\n:: {outer_cond} ->\n  do\n  :: {inner_cond} ->\n    {inner_body}\n  :: else -> break\n  od;\n  {outer_body}\n:: else -> break\nod"
            },
            "complex_conditional_error": {
                "pattern": "Invalid complex conditional",
                "fix_description": "Convert complex conditionals to Promela if...fi format",
                "example": "if\n:: {cond1} -> {body1}\n:: {cond2} -> {body2}\n:: else -> {else_body}\nfi"
            },
            "memory_management_error": {
                "pattern": "Invalid memory management",
                "fix_description": "Convert malloc/free to array operations",
                "example": "byte {name}[{size}]"
            },
            "process_sync_error": {
                "pattern": "Invalid process synchronization",
                "fix_description": "Convert mutex operations to channel operations",
                "example": "chan {name} = [1] of {byte}"
            },
            "channel_op_error": {
                "pattern": "Invalid channel operation",
                "fix_description": "Fix channel send/receive operations",
                "example": "{chan}!{value} or {chan}?{var}"
            },
            "deadlock_error": {
                "pattern": "Potential deadlock detected",
                "fix_description": "Add timeout and progress labels",
                "example": "do\n:: timeout -> break\n:: {cond} -> {body}\nod"
            },
            "livelock_error": {
                "pattern": "Potential livelock detected",
                "fix_description": "Add fairness constraints",
                "example": "do\n:: (true) -> break\n:: {cond} -> {body}\nod"
            },
            "race_condition_error": {
                "pattern": "Potential race condition detected",
                "fix_description": "Add atomic blocks for critical sections",
                "example": "atomic {{ {critical_section} }}"
            }
        }
        
        for pattern_id, pattern_info in patterns.items():
            self.add_error_pattern(
                pattern_id,
                pattern_info["pattern"],
                pattern_info["fix_description"],
                pattern_info["example"]
            )
    
    def add_error_pattern(self, 
                         pattern_id: str,
                         error_pattern: str,
                         fix_description: str,
                         example: str):
        """Add a new error pattern with its fix."""
        if pattern_id not in self.error_patterns:
            self.error_patterns[pattern_id] = []
        
        self.error_patterns[pattern_id].append({
            "pattern": error_pattern,
            "fix_description": fix_description,
            "example": example,
            "success_count": 0,
            "last_updated": datetime.now().isoformat()
        })
    
    def add_fix_pattern(self,
                       pattern_id: str,
                       fix_pattern: str,
                       success_rate: float = 0.0):
        """Add a new fix pattern."""
        if pattern_id not in self.fix_patterns:
            self.fix_patterns[pattern_id] = []
        
        self.fix_patterns[pattern_id].append({
            "pattern": fix_pattern,
            "success_rate": success_rate,
            "last_updated": datetime.now().isoformat()
        })
    
    def record_successful_fix(self, pattern_id: str):
        """Record a successful fix for a pattern."""
        if pattern_id in self.successful_fixes:
            self.successful_fixes[pattern_id] += 1
        else:
            self.successful_fixes[pattern_id] = 1
        
        # Update success count in error patterns
        if pattern_id in self.error_patterns:
            for pattern in self.error_patterns[pattern_id]:
                pattern["success_count"] += 1
                pattern["last_updated"] = datetime.now().isoformat()
    
    def get_fix_for_error(self, error_message: str) -> Optional[Dict[str, Any]]:
        """Get the most successful fix for an error message."""
        best_match = None
        highest_success = -1
        
        for pattern_id, patterns in self.error_patterns.items():
            for pattern in patterns:
                if pattern["pattern"] in error_message:
                    success_count = pattern["success_count"]
                    if success_count > highest_success:
                        highest_success = success_count
                        best_match = {
                            "pattern_id": pattern_id,
                            "fix_description": pattern["fix_description"],
                            "example": pattern["example"]
                        }
        
        return best_match
    
    def _load_data(self):
        """Load error patterns and fix patterns from disk."""
        error_file = os.path.join(self.db_path, "error_patterns.json")
        fix_file = os.path.join(self.db_path, "fix_patterns.json")
        
        if os.path.exists(error_file):
            with open(error_file, 'r') as f:
                self.error_patterns = json.load(f)
        
        if os.path.exists(fix_file):
            with open(fix_file, 'r') as f:
                self.fix_patterns = json.load(f)
    
    def save_data(self):
        """Save error patterns and fix patterns to disk."""
        error_file = os.path.join(self.db_path, "error_patterns.json")
        fix_file = os.path.join(self.db_path, "fix_patterns.json")
        
        with open(error_file, 'w') as f:
            json.dump(self.error_patterns, f, indent=2)
        
        with open(fix_file, 'w') as f:
            json.dump(self.fix_patterns, f, indent=2)
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get statistics about error patterns and fixes."""
        total_patterns = len(self.error_patterns)
        total_fixes = len(self.fix_patterns)
        total_successes = sum(self.successful_fixes.values())
        
        return {
            "total_patterns": total_patterns,
            "total_fixes": total_fixes,
            "total_successes": total_successes,
            "success_rate": total_successes / total_patterns if total_patterns > 0 else 0
        } 