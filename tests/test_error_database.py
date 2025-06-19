import unittest
import os
import tempfile
import shutil
from core.error_database import ErrorDatabase

class TestErrorDatabase(unittest.TestCase):
    def setUp(self):
        """Set up test environment."""
        self.test_dir = tempfile.mkdtemp()
        self.db = ErrorDatabase(self.test_dir)

    def tearDown(self):
        """Clean up test environment."""
        shutil.rmtree(self.test_dir)

    def test_add_error_pattern(self):
        """Test adding an error pattern."""
        error_id = self.db.add_error_pattern(
            error_type="syntax_error",
            error_context="if statement",
            error_message="Invalid syntax",
            line_number=10
        )
        self.assertIsNotNone(error_id)
        
        # Verify the error pattern was added
        error_data = self.db._read_json(self.db.error_patterns_file)
        self.assertEqual(len(error_data["error_patterns"]), 1)
        self.assertEqual(error_data["error_patterns"][0]["error_type"], "syntax_error")

    def test_add_fix_pattern(self):
        """Test adding a fix pattern."""
        # First add an error pattern
        error_id = self.db.add_error_pattern(
            error_type="syntax_error",
            error_context="if statement",
            error_message="Invalid syntax"
        )
        
        # Then add a fix pattern
        fix_id = self.db.add_fix_pattern(
            error_pattern_id=error_id,
            fix_type="syntax_fix",
            fix_description="Convert to Promela syntax",
            original_code="if (x > 0) { y = 1; }",
            fixed_code="if\n:: x > 0 -> y = 1\nfi"
        )
        self.assertIsNotNone(fix_id)
        
        # Verify the fix pattern was added
        fix_data = self.db._read_json(self.db.fix_patterns_file)
        self.assertEqual(len(fix_data["fix_patterns"]), 1)
        self.assertEqual(fix_data["fix_patterns"][0]["fix_type"], "syntax_fix")

    def test_find_similar_errors(self):
        """Test finding similar errors."""
        # Add some test data
        error_id = self.db.add_error_pattern(
            error_type="syntax_error",
            error_context="if statement",
            error_message="Invalid syntax"
        )
        
        self.db.add_fix_pattern(
            error_pattern_id=error_id,
            fix_type="syntax_fix",
            fix_description="Convert to Promela syntax",
            original_code="if (x > 0) { y = 1; }",
            fixed_code="if\n:: x > 0 -> y = 1\nfi"
        )
        
        # Find similar errors
        similar_errors = self.db.find_similar_errors("syntax_error", "if statement")
        self.assertEqual(len(similar_errors), 1)
        self.assertEqual(similar_errors[0]["error_type"], "syntax_error")

    def test_add_test_case(self):
        """Test adding a test case."""
        test_id = self.db.add_test_case(
            name="Basic If Test",
            description="Test basic if statement conversion",
            input_code="if (x > 0) { y = 1; }",
            expected_output="if\n:: x > 0 -> y = 1\nfi"
        )
        self.assertIsNotNone(test_id)
        
        # Verify the test case was added
        test_data = self.db._read_json(self.db.test_cases_file)
        self.assertEqual(len(test_data["test_cases"]), 1)
        self.assertEqual(test_data["test_cases"][0]["name"], "Basic If Test")

    def test_add_test_result(self):
        """Test adding a test result."""
        # First add required data
        error_id = self.db.add_error_pattern(
            error_type="syntax_error",
            error_context="if statement",
            error_message="Invalid syntax"
        )
        
        fix_id = self.db.add_fix_pattern(
            error_pattern_id=error_id,
            fix_type="syntax_fix",
            fix_description="Convert to Promela syntax",
            original_code="if (x > 0) { y = 1; }",
            fixed_code="if\n:: x > 0 -> y = 1\nfi"
        )
        
        test_id = self.db.add_test_case(
            name="Basic If Test",
            description="Test basic if statement conversion",
            input_code="if (x > 0) { y = 1; }",
            expected_output="if\n:: x > 0 -> y = 1\nfi"
        )
        
        # Add test result
        result_id = self.db.add_test_result(
            test_case_id=test_id,
            error_pattern_id=error_id,
            fix_pattern_id=fix_id,
            success=True,
            execution_time=0.1
        )
        self.assertIsNotNone(result_id)
        
        # Verify the test result was added
        result_data = self.db._read_json(self.db.test_results_file)
        self.assertEqual(len(result_data["test_results"]), 1)
        self.assertTrue(result_data["test_results"][0]["success"])

    def test_update_fix_success_rate(self):
        """Test updating fix success rate."""
        # Add test data
        error_id = self.db.add_error_pattern(
            error_type="syntax_error",
            error_context="if statement",
            error_message="Invalid syntax"
        )
        
        fix_id = self.db.add_fix_pattern(
            error_pattern_id=error_id,
            fix_type="syntax_fix",
            fix_description="Convert to Promela syntax",
            original_code="if (x > 0) { y = 1; }",
            fixed_code="if\n:: x > 0 -> y = 1\nfi"
        )
        
        test_id = self.db.add_test_case(
            name="Basic If Test",
            description="Test basic if statement conversion",
            input_code="if (x > 0) { y = 1; }",
            expected_output="if\n:: x > 0 -> y = 1\nfi"
        )
        
        # Add test results
        self.db.add_test_result(
            test_case_id=test_id,
            error_pattern_id=error_id,
            fix_pattern_id=fix_id,
            success=True,
            execution_time=0.1
        )
        
        self.db.add_test_result(
            test_case_id=test_id,
            error_pattern_id=error_id,
            fix_pattern_id=fix_id,
            success=False,
            execution_time=0.1
        )
        
        # Update success rate
        self.db.update_fix_success_rate(fix_id)
        
        # Verify the success rate was updated
        fix_data = self.db._read_json(self.db.fix_patterns_file)
        fix = next(f for f in fix_data["fix_patterns"] if f["id"] == fix_id)
        self.assertEqual(fix["success_rate"], 0.5)

    def test_complex_test_cases(self):
        """Test complex test cases with multiple patterns."""
        # Add multiple error patterns
        error_ids = []
        for i in range(3):
            error_id = self.db.add_error_pattern(
                error_type=f"error_type_{i}",
                error_context=f"context_{i}",
                error_message=f"message_{i}"
            )
            error_ids.append(error_id)
            
            # Add fix pattern for each error
            self.db.add_fix_pattern(
                error_pattern_id=error_id,
                fix_type=f"fix_type_{i}",
                fix_description=f"description_{i}",
                original_code=f"original_{i}",
                fixed_code=f"fixed_{i}"
            )
        
        # Add test case
        test_id = self.db.add_test_case(
            name="Complex Test",
            description="Test multiple patterns",
            input_code="test code",
            expected_output="expected output"
        )
        
        # Add test results
        for error_id in error_ids:
            self.db.add_test_result(
                test_case_id=test_id,
                error_pattern_id=error_id,
                fix_pattern_id=error_id,  # Using error_id as fix_id for simplicity
                success=True,
                execution_time=0.1
            )
        
        # Verify all data was added correctly
        error_data = self.db._read_json(self.db.error_patterns_file)
        fix_data = self.db._read_json(self.db.fix_patterns_file)
        test_data = self.db._read_json(self.db.test_cases_file)
        result_data = self.db._read_json(self.db.test_results_file)
        
        self.assertEqual(len(error_data["error_patterns"]), 3)
        self.assertEqual(len(fix_data["fix_patterns"]), 3)
        self.assertEqual(len(test_data["test_cases"]), 1)
        self.assertEqual(len(result_data["test_results"]), 3)

if __name__ == '__main__':
    unittest.main() 