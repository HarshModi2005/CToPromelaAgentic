#!/usr/bin/env python3
"""
Unified test framework for CIL to Promela converter.
Consolidates functionality from multiple test scripts:
- run_all_tests.py
- run_tests.py
- test_agent.py
- test_case_manager.py
- test_conversion_custom.py
- test_conversion.py
- test_error_database.py
- test_multi_conversion.py
- test_suite_generator.py
"""

import os
import sys
import json
import logging
import argparse
import subprocess
import tempfile
import datetime
from typing import Dict, List, Any, Tuple, Optional

from core.agent import CILToPromelaConverter
from core.error_database import ErrorDatabase

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger('TestUnified')


class TestManager:
    """Unified test manager that consolidates functionality from all test scripts."""
    
    def __init__(self, api_key: str, model: str = "gemini-2.0-flash",
                 log_dir: str = "logs", results_dir: str = "results",
                 test_cases_dir: str = "test_cases"):
        """
        Initialize the test manager.
        
        Args:
            api_key: API key for the LLM service
            model: Model name to use
            log_dir: Directory for logs
            results_dir: Directory for results
            test_cases_dir: Directory for test cases
        """
        self.api_key = api_key
        self.model = model
        self.log_dir = log_dir
        self.results_dir = results_dir
        self.test_cases_dir = test_cases_dir
        
        # Create converter
        self.converter = CILToPromelaConverter(
            api_key=api_key,
            model=model,
            spin_path="spin",
            verification_target="general",
            advanced_features=True,
            reduction_techniques=["partial_order", "collapse", "minimize"],
            max_iterations=10
        )
        
        # Create error database
        self.error_db = ErrorDatabase()
        
        # Create directories
        os.makedirs(log_dir, exist_ok=True)
        os.makedirs(results_dir, exist_ok=True)
        
    def run_single_test(self, cil_file: str, output_file: str = None) -> Tuple[bool, str]:
        """
        Run a single test on a CIL file.
        
        Args:
            cil_file: Path to the CIL file
            output_file: Path to save Promela output (optional)
            
        Returns:
            Tuple of (success, message)
        """
        logger.info(f"Testing conversion of {cil_file}")
        
        try:
            # Process the file
            success, message = self.converter.process_cil_file(cil_file, output_file)
            
            if success:
                logger.info(f"✅ Conversion successful: {message}")
            else:
                logger.error(f"❌ Conversion failed: {message}")
                
            return success, message
            
        except Exception as e:
            logger.error(f"Error processing {cil_file}: {e}")
            return False, str(e)
    
    def run_all_tests(self) -> Dict[str, Any]:
        """
        Run tests on all CIL files in the test cases directory.
        
        Returns:
            Dictionary with test results
        """
        # Get all test cases
        test_cases = []
        
        # Add test cases from test_cases directory
        for file in os.listdir(self.test_cases_dir):
            if file.endswith(".cil"):
                test_cases.append(os.path.join(self.test_cases_dir, file))
        
        # Add test cases from cil_test_files directory if it exists
        cil_test_files_dir = "cil_test_files"
        if os.path.exists(cil_test_files_dir):
            for file in os.listdir(cil_test_files_dir):
                if file.endswith(".cil"):
                    test_cases.append(os.path.join(cil_test_files_dir, file))
        
        # Run all test cases
        total_tests = len(test_cases)
        passed_tests = 0
        test_results = []
        
        logger.info(f"Starting test suite with {total_tests} test cases")
        
        for test_file in test_cases:
            # Process each test file
            output_file = os.path.join(self.results_dir, f"{os.path.basename(test_file).replace('.cil', '.pml')}")
            success, message = self.run_single_test(test_file, output_file)
            
            if success:
                passed_tests += 1
                
            # Record test result
            test_results.append({
                "test_file": test_file,
                "output_file": output_file,
                "success": success,
                "message": message,
                "timestamp": datetime.datetime.now().isoformat()
            })
        
        # Prepare results
        results = {
            "timestamp": datetime.datetime.now().isoformat(),
            "total_tests": total_tests,
            "passed_tests": passed_tests,
            "failed_tests": total_tests - passed_tests,
            "test_results": test_results
        }
        
        # Save results
        self._save_results(results)
        
        return results
    
    def run_multi_file_test(self, cil_files: List[str], output_dir: str = None) -> Tuple[bool, Dict]:
        """
        Test conversion of multiple connected CIL files to Promela.
        
        Args:
            cil_files: List of CIL files to process together
            output_dir: Directory to save output files (optional)
            
        Returns:
            Tuple of (overall_success, file_results)
        """
        if output_dir is None:
            output_dir = self.results_dir
            
        os.makedirs(output_dir, exist_ok=True)
        
        # Process the files
        logger.info(f"Processing {len(cil_files)} CIL files together...")
        results = self.converter.process_cil_files(cil_files, output_dir)
        
        # Report results
        success_count = sum(1 for success, _ in results.values() if success)
        logger.info(f"Conversion results: {success_count}/{len(cil_files)} files successfully converted")
        
        for file_path, (success, message) in results.items():
            status = "✓" if success else "✗"
            logger.info(f"{status} {os.path.basename(file_path)}: {message[:100]}...")
        
        # Check for merged file
        merged_file = os.path.join(output_dir, "merged_model.pml")
        if os.path.exists(merged_file):
            logger.info(f"Merged model created at {merged_file}")
        
        return success_count == len(cil_files), results
    
    def verify_promela_code(self, promela_code: str) -> Tuple[bool, str]:
        """
        Verify Promela code with Spin.
        
        Args:
            promela_code: Promela code to verify
            
        Returns:
            Tuple of (success, message)
        """
        with tempfile.NamedTemporaryFile(suffix='.pml', delete=False) as tmp:
            tmp_filename = tmp.name
            tmp.write(promela_code.encode('utf-8'))
        
        try:
            # Run spin to check syntax
            result = subprocess.run(['spin', '-a', tmp_filename], 
                                   capture_output=True, text=True)
            
            if result.returncode == 0:
                logger.info("SPIN verification passed: Promela code is syntactically valid")
                return True, "Valid"
            else:
                logger.error("SPIN verification failed: Promela code has syntax errors")
                logger.error(result.stderr)
                return False, result.stderr
        finally:
            # Clean up temporary file
            os.unlink(tmp_filename)
    
    def generate_report(self, results: Dict[str, Any]) -> str:
        """
        Generate a human-readable test report.
        
        Args:
            results: Test results dictionary
            
        Returns:
            Report as a string
        """
        report = []
        report.append("Test Results Report")
        report.append("=" * 50)
        report.append(f"Total Tests: {results['total_tests']}")
        report.append(f"Passed: {results['passed_tests']}")
        report.append(f"Failed: {results['failed_tests']}")
        
        if results['total_tests'] > 0:
            success_rate = (results['passed_tests'] / results['total_tests'] * 100)
            report.append(f"Success Rate: {success_rate:.2f}%")
        
        report.append("\nDetailed Results:")
        report.append("-" * 50)
        
        for test_result in results["test_results"]:
            status = "✓" if test_result["success"] else "✗"
            report.append(f"{status} {os.path.basename(test_result['test_file'])}")
            if not test_result["success"]:
                report.append(f"  Error: {test_result['message'][:100]}...")
        
        return "\n".join(report)
    
    def _save_results(self, results: Dict[str, Any]):
        """
        Save test results to file.
        
        Args:
            results: Test results to save
        """
        timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        results_file = os.path.join(self.results_dir, f"test_results_{timestamp}.json")
        
        with open(results_file, 'w') as f:
            json.dump(results, f, indent=2)
        
        # Also save as latest.json
        latest_file = os.path.join(self.results_dir, "latest.json")
        with open(latest_file, 'w') as f:
            json.dump(results, f, indent=2)
            
        logger.info(f"Saved test results to {results_file}")
    
    def get_error_database_stats(self) -> Dict[str, Any]:
        """
        Get statistics from the error database.
        
        Returns:
            Dictionary with error database statistics
        """
        stats = {
            "error_patterns": 0,
            "fix_patterns": 0,
            "autofix_successes": 0
        }
        
        # Check error patterns
        error_patterns_file = os.path.join(self.log_dir, "error_patterns.json")
        if os.path.exists(error_patterns_file):
            with open(error_patterns_file, 'r') as f:
                error_patterns = json.load(f)
                stats["error_patterns"] = len(error_patterns.get("error_patterns", []))
        
        # Check fix patterns
        fix_patterns_file = os.path.join(self.log_dir, "fix_patterns.json")
        if os.path.exists(fix_patterns_file):
            with open(fix_patterns_file, 'r') as f:
                fix_patterns = json.load(f)
                stats["fix_patterns"] = len(fix_patterns.get("fix_patterns", []))
        
        # Check autofix successes
        autofix_file = os.path.join(self.log_dir, "autofix_successes.json")
        if os.path.exists(autofix_file):
            with open(autofix_file, 'r') as f:
                autofix_successes = json.load(f)
                stats["autofix_successes"] = len(autofix_successes.get("fixes", []))
                
        return stats


def main():
    """Main function."""
    parser = argparse.ArgumentParser(description="Unified test framework for CIL to Promela converter")
    
    # Test mode selection
    mode_group = parser.add_mutually_exclusive_group(required=True)
    mode_group.add_argument("--single", "-s", help="Run a single test on a CIL file")
    mode_group.add_argument("--all", "-a", action="store_true", help="Run all tests")
    mode_group.add_argument("--multi", "-m", nargs="+", help="Run multi-file test with the specified CIL files")
    
    # Common options
    parser.add_argument("--output", "-o", help="Output file or directory")
    parser.add_argument("--api-key", default="AIzaSyC88vGjUkqyu4Ux_9zVCdk7Z88cpQi7uEM", 
                        help="API key for LLM service")
    parser.add_argument("--model", default="gemini-2.0-flash", help="Model to use")
    parser.add_argument("--verbose", "-v", action="store_true", help="Enable verbose logging")
    
    args = parser.parse_args()
    
    # Set log level
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
        
    # Create test manager
    test_manager = TestManager(args.api_key, args.model)
    
    # Run tests based on mode
    if args.single:
        # Run single test
        output_file = args.output or args.single.replace('.cil', '.pml')
        success, message = test_manager.run_single_test(args.single, output_file)
        
        if success:
            print(f"✅ Test passed: {message}")
            sys.exit(0)
        else:
            print(f"❌ Test failed: {message}")
            sys.exit(1)
            
    elif args.all:
        # Run all tests
        results = test_manager.run_all_tests()
        report = test_manager.generate_report(results)
        print(report)
        
        # Get error database stats
        stats = test_manager.get_error_database_stats()
        print("\nError Database Statistics:")
        print(f"Error Patterns: {stats['error_patterns']}")
        print(f"Fix Patterns: {stats['fix_patterns']}")
        print(f"Autofix Successes: {stats['autofix_successes']}")
        
        sys.exit(0 if results["failed_tests"] == 0 else 1)
        
    elif args.multi:
        # Run multi-file test
        output_dir = args.output or "output"
        success, results = test_manager.run_multi_file_test(args.multi, output_dir)
        
        if success:
            print(f"✅ All files converted successfully")
            sys.exit(0)
        else:
            print(f"❌ Some files failed to convert")
            sys.exit(1)


if __name__ == "__main__":
    main() 