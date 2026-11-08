"""Real Lean proof terms exercise the individual-theorem verification gate."""

import subprocess
import unittest

from prototype_audit import AuditError, LEAN, lean_metadata
from verify import check_theorems


class VerifyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        subprocess.run(["lake", "build", "PtxPrototype.Audit"], cwd=LEAN, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        cls.names = [f"IndividualVerifyFixture.{name}" for name in ["proved", "withGap", "withSorry", "data"]]
        cls.declarations, _ = lean_metadata([], names=cls.names, source_before_audit="""
namespace IndividualVerifyFixture
theorem proved (n : Nat) : n + 0 = n := Nat.add_zero n
axiom unfinished : True
theorem withGap : True := unfinished
theorem withSorry : True := by sorry
def data : Nat := 42
end IndividualVerifyFixture
""")

    def test_checked_proof_passes(self):
        check_theorems(self.declarations, [self.names[0]])

    def test_named_gap_is_not_a_strict_proof(self):
        with self.assertRaisesRegex(AuditError, "unproved assumptions.*unfinished"):
            check_theorems(self.declarations, [self.names[1]])

    def test_sorry_is_not_a_strict_proof(self):
        with self.assertRaisesRegex(AuditError, "unproved assumptions.*sorryAx"):
            check_theorems(self.declarations, [self.names[2]])

    def test_program_data_is_not_a_proof(self):
        with self.assertRaisesRegex(AuditError, "not a proof theorem"):
            check_theorems(self.declarations, [self.names[3]])


if __name__ == "__main__":
    unittest.main()
