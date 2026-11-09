"""Actual Lean regressions for strict proof metadata and acceptance inventories."""

import copy
from pathlib import Path
import tomllib
import unittest

from proof_audit import AuditError, classify_cases, lean_metadata, valid_name, validate_manifest

FIXTURE = """
namespace ProofAuditFixture
theorem proved : True := True.intro
axiom gap : True
theorem withGap : True := gap
theorem helperWithSorry : True := by sorry
theorem viaHelper : True := helperWithSorry
theorem transitive : True := viaHelper
def data : Nat := 42
end ProofAuditFixture
"""
NAMES = ["proved", "gap", "withGap", "helperWithSorry", "viaHelper", "transitive", "data"]


class ProofAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.declarations, _ = lean_metadata(["Init"],
            names=[f"ProofAuditFixture.{name}" for name in NAMES], source_before_audit=FIXTURE)

    def case(self, name="proved"):
        return [{"id": "fixture", "scope": "Metadata regression only",
                 "correctness": [f"ProofAuditFixture.{name}"],
                 "nonvacuity": [], "instances": []}]

    def test_transitive_sorry_dependencies_are_visible(self):
        self.assertIn("sorryAx", self.declarations["ProofAuditFixture.transitive"]["axioms"])

    def test_finished_proof_is_strict_despite_unrelated_holes(self):
        result = classify_cases(self.case(), self.declarations)
        self.assertEqual(result[0]["status"], "strict-proof")
        self.assertEqual(result[0]["assumptions"], [])

    def test_sorry_and_named_axioms_cannot_pass(self):
        for name in ("withGap", "helperWithSorry", "viaHelper", "transitive"):
            with self.subTest(name=name), self.assertRaisesRegex(AuditError, "unproved assumptions"):
                classify_cases(self.case(name), self.declarations)

    def test_data_and_axioms_are_not_proof_theorems(self):
        for name in ("data", "gap"):
            with self.subTest(name=name), self.assertRaisesRegex(AuditError, "proved as a theorem"):
                classify_cases(self.case(name), self.declarations)

    def test_missing_declaration_fails(self):
        with self.assertRaises(AuditError):
            lean_metadata(["Init"], names=["Missing.declaration"])

    def test_names_cannot_inject_lean_commands(self):
        with self.assertRaises(AuditError):
            valid_name("Ptx.Test\\naxiom injected : False")

    def manifest(self):
        return tomllib.loads((Path(__file__).resolve().parent.parent / "prototype.toml").read_text())

    def test_original_cases_and_capabilities_are_retained(self):
        manifest = self.manifest()
        validate_manifest(manifest)
        for group in ("cases", "capability_claims"):
            broken = copy.deepcopy(manifest)
            if group == "cases":
                broken[group].pop()
            else:
                broken[group].popitem()
            with self.subTest(group=group), self.assertRaises(AuditError):
                validate_manifest(broken)

    def test_unsupported_needs_boolean_and_reason(self):
        for value in ("false", True):
            manifest = self.manifest()
            manifest["cases"][0]["unsupported"] = value
            with self.subTest(value=value), self.assertRaises(AuditError):
                validate_manifest(manifest)

    def test_removed_registry_settings_are_rejected(self):
        for name, value in (("assumptions", []), ("overrides", {}), ("imports", ["Ptx"])):
            manifest = self.manifest()
            manifest[name] = value
            with self.subTest(name=name), self.assertRaises(AuditError):
                validate_manifest(manifest)


if __name__ == "__main__":
    unittest.main()
