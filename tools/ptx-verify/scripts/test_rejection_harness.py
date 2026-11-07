"""Do not confuse failed elaboration or an unrelated failure with refutation."""
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
import tempfile
import unittest

from check import check_decide_rejections


class RejectionHarnessTests(unittest.TestCase):
    def check_cases(self, cases):
        with tempfile.TemporaryDirectory(prefix="ptx-rejection-harness-") as directory:
            with redirect_stdout(StringIO()):
                check_decide_rejections(Path(directory), "import Init", cases)

    def test_each_false_assertion_has_its_own_refutation(self):
        self.check_cases({"first": "(1 : Nat) = 2", "second": "(2 : Nat) = 3"})

    def test_batch_exceeds_the_default_error_limit(self):
        self.check_cases({f"false_{i}": "(1 : Nat) = 2" for i in range(105)})

    def test_true_assertion_does_not_count_as_refuted(self):
        with self.assertRaises(SystemExit):
            self.check_cases({"true": "(1 : Nat) = 1"})

    def test_other_refutation_cannot_hide_a_true_assertion(self):
        with self.assertRaises(SystemExit):
            self.check_cases({"false": "(1 : Nat) = 2", "true": "(1 : Nat) = 1"})

    def test_elaboration_failure_is_not_refutation(self):
        with self.assertRaises(SystemExit):
            self.check_cases({"ill_typed": "missing_proposition"})

    def test_parse_failure_is_not_refutation(self):
        with self.assertRaises(SystemExit):
            self.check_cases({"bad_syntax": "Nat.succ ("})
