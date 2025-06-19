import os
import logging
from typing import List, Dict, Any

class TestSuiteGenerator:
    def __init__(self):
        self.test_cases = []
    
    def generate_test_suite(self):
        """Generate the complete test suite."""
        # Clear existing test cases
        self.test_cases = []
        
        # Add all test cases
        self.test_cases.extend(self._load_test_files("basic"))
        self.test_cases.extend(self._load_test_files("intermediate"))
        self.test_cases.extend(self._load_test_files("advanced"))
        self.test_cases.extend(self._load_test_files("verification"))
        
        return self.test_cases
    
    def _load_test_files(self, category: str) -> List[Dict[str, Any]]:
        """Load test cases from files in the specified category directory."""
        test_cases = []
        category_dir = f"test_suite/{category}"
        
        if not os.path.exists(category_dir):
            return test_cases
        
        for filename in os.listdir(category_dir):
            if filename.endswith(".cil"):
                file_path = os.path.join(category_dir, filename)
                try:
                    with open(file_path, 'r') as f:
                        cil_code = f.read()
                        test_case = {
                            'name': f"{category}_{filename[:-4]}",
                            'description': f"Test case from {filename}",
                            'cil_code': cil_code,
                            'category': category
                        }
                        test_cases.append(test_case)
                except Exception as e:
                    logging.error(f"Error loading test case {filename}: {e}")
        
        return test_cases 