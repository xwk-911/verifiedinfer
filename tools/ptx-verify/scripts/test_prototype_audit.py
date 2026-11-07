"""Exercise the actual Lean dependency exporter and prototype trust boundary."""

import unittest
import copy
from pathlib import Path
import tomllib

from prototype_audit import (AuditError, audit_registered_assumptions, classify_cases, digest_type,
                             forbidden_assumption_dependencies, lean_metadata, valid_name, validate_manifest)


FIXTURE = """
namespace PtxPrototype.Assumptions
axiom add_comm : ∀ a b : Nat, a+b = b+a
end PtxPrototype.Assumptions
namespace PtxPrototype.Test
theorem reference : ∀ n : Nat, n+1 = 1+n := by intro n; exact Nat.add_comm n 1
theorem conditional : ∀ n : Nat, n+1 = 1+n := fun n => PtxPrototype.Assumptions.add_comm n 1
theorem transitive : ∀ n : Nat, n+1 = 1+n := conditional
theorem strict : True := True.intro
end PtxPrototype.Test
"""
AUX = "PtxPrototype.Assumptions.add_comm"
REF = "PtxPrototype.Test.reference"
COND = "PtxPrototype.Test.conditional"
TRANSITIVE = "PtxPrototype.Test.transitive"
STRICT = "PtxPrototype.Test.strict"


class PrototypeAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        _, cls.baseline = lean_metadata(["Init"])
        cls.declarations, cls.inventory = lean_metadata(["Init"], names=[AUX, STRICT],
            comparisons=[(COND, REF), (TRANSITIVE, REF)], source_before_audit=FIXTURE,
            auxiliary_type_checks=[(AUX, REF), (AUX, COND)])

    def registry(self, affected=None):
        declaration = self.declarations[AUX]
        return [{"name": AUX, "role": "arithmetic", "statement": declaration["statement"],
                 "type_sha256": digest_type(declaration), "purpose": "Fixture of a local arithmetic lemma",
                 "review": "No VC/program/specification is assumed", "discharge_task": "Prove Nat.add_comm",
                 "affected_vcs": affected or [COND]}]

    def case(self, name=COND):
        return [{"id": "fixture", "scope": "Synthetic test, never a kernel acceptance result",
                 "correctness": [name], "nonvacuity": [STRICT], "instances": [STRICT]}]

    def test_transitive_axioms_are_extracted_from_checked_proof_terms(self):
        self.assertIn(AUX, self.declarations[TRANSITIVE]["axioms"])
        self.assertTrue(self.declarations[TRANSITIVE]["matches_reference"])

    def test_registered_auxiliary_gives_conditional_status_and_exact_impact(self):
        registry = self.registry()
        audit_registered_assumptions(registry, self.declarations, self.inventory-self.baseline, {REF, COND})
        result = classify_cases(self.case(), self.declarations, registry)
        self.assertEqual(result[0]["status"], "conditional-proof")
        self.assertEqual(result[0]["assumptions"], [AUX])

    def test_no_holes_remains_strict(self):
        result = classify_cases(self.case(STRICT), self.declarations, [])
        self.assertEqual(result[0]["status"], "strict-proof")

    def test_unregistered_axiom_is_rejected(self):
        with self.assertRaises(AuditError):
            classify_cases(self.case(), self.declarations, [])

    def test_unused_unregistered_axiom_is_rejected(self):
        with self.assertRaises(AuditError):
            audit_registered_assumptions(self.registry(), self.declarations, {AUX, "Hidden.unused"}, {REF})

    def test_changed_statement_and_type_fingerprint_are_rejected(self):
        for field in ("statement", "type_sha256"):
            registry = self.registry()
            registry[0][field] += "changed"
            with self.subTest(field=field), self.assertRaises(AuditError):
                audit_registered_assumptions(registry, self.declarations, {AUX}, {REF, COND})

    def test_stale_impact_list_is_rejected(self):
        with self.assertRaises(AuditError):
            classify_cases(self.case(), self.declarations, self.registry([TRANSITIVE]))

    def test_anonymous_sorry_does_not_pass(self):
        name = "PtxPrototype.Test.anonymous"
        declarations, _ = lean_metadata(["Init"], names=[name, STRICT],
            source_before_audit=FIXTURE + f"\ntheorem {name} : True := by sorry\n")
        with self.assertRaises(AuditError):
            classify_cases(self.case(name), declarations, [])

    def test_wrong_vc_type_is_rejected(self):
        declarations, _ = lean_metadata(["Init"], names=[STRICT], comparisons=[(COND, STRICT)], source_before_audit=FIXTURE)
        self.assertFalse(declarations[COND]["matches_reference"])
        with self.assertRaises(AuditError):
            classify_cases(self.case(), declarations, self.registry())

    def test_top_vc_cannot_itself_be_an_axiom(self):
        with self.assertRaises(AuditError):
            classify_cases(self.case(AUX), self.declarations, self.registry([AUX]))

    def test_renamed_assumption_with_identical_vc_type_is_rejected(self):
        name = "PtxPrototype.Assumptions.renamedVC"
        source = FIXTURE + f"\naxiom {name} : ∀ n : Nat, n+1 = 1+n\n"
        declarations, _ = lean_metadata(["Init"], names=[name], source_before_audit=source,
            auxiliary_type_checks=[(name, REF)])
        declaration = declarations[name]
        self.assertEqual(declaration["matches_protected_types"], [REF])
        registry = [{**self.registry()[0], "name": name, "statement": declaration["statement"],
                     "type_sha256": digest_type(declaration)}]
        with self.assertRaises(AuditError):
            audit_registered_assumptions(registry, declarations, {name}, {REF})

    def test_definition_and_structure_vc_wrappers_are_detected(self):
        definitions = """
namespace Ptx
def Triple (goal : Prop) : Prop := goal
end Ptx
namespace PtxPrototype.Test
def hiddenGoal : Prop := Ptx.Triple True
structure WrappedGoal : Prop where
  result : Ptx.Triple True
end PtxPrototype.Test
namespace PtxPrototype.Assumptions
axiom hidden : PtxPrototype.Test.hiddenGoal
axiom wrapped : PtxPrototype.Test.WrappedGoal
end PtxPrototype.Assumptions
def ArbitraryNamespace.hiddenGoal : Prop := Ptx.Triple True
axiom PtxPrototype.Assumptions.otherNamespace : ArbitraryNamespace.hiddenGoal
"""
        names = ["PtxPrototype.Assumptions.hidden", "PtxPrototype.Assumptions.wrapped", "PtxPrototype.Assumptions.otherNamespace"]
        declarations, _ = lean_metadata(["Init"], names=names, source_before_audit=definitions)
        for name in names:
            with self.subTest(name=name):
                self.assertIn("Ptx.Triple", forbidden_assumption_dependencies(declarations[name], set()))

    def test_false_and_fixed_generated_program_assumptions_are_detected(self):
        definitions = """
def Ptx.Generated.Test.program : Nat := 0
axiom PtxPrototype.Assumptions.falsehood : False
axiom PtxPrototype.Assumptions.fixedProgram : Ptx.Generated.Test.program = 0
"""
        names = ["PtxPrototype.Assumptions.falsehood", "PtxPrototype.Assumptions.fixedProgram"]
        declarations, _ = lean_metadata(["Init"], names=names, source_before_audit=definitions)
        for name in names:
            with self.subTest(name=name):
                self.assertTrue(forbidden_assumption_dependencies(declarations[name], set()))

    def test_missing_declaration_is_a_failure(self):
        with self.assertRaises(AuditError):
            lean_metadata(["Init"], names=["Missing.declaration"])

    def test_names_cannot_inject_lean_commands(self):
        with self.assertRaises(AuditError):
            valid_name("Ptx.Test\naxiom injected : False")

    def manifest(self):
        return tomllib.loads((Path(__file__).resolve().parent.parent / "prototype.toml").read_text())

    def test_acceptance_cannot_drop_an_original_case_or_capability(self):
        manifest = self.manifest()
        validate_manifest(manifest)
        missing_case = copy.deepcopy(manifest)
        missing_case["cases"].pop()
        missing_capability = copy.deepcopy(manifest)
        missing_capability["capability_claims"].popitem()
        for broken in (missing_case, missing_capability):
            with self.assertRaises(AuditError):
                validate_manifest(broken)

    def test_overrides_must_stay_in_the_prototype_library(self):
        manifest = self.manifest()
        manifest["overrides"] = {manifest["cases"][0]["correctness"][0]: STRICT}
        validate_manifest(manifest)
        manifest["overrides"] = {manifest["cases"][0]["correctness"][0]: "Ptx.UnreviewedProof"}
        with self.assertRaises(AuditError):
            validate_manifest(manifest)

    def test_unsupported_needs_boolean_and_reason(self):
        for value in ("false", True):
            manifest = self.manifest()
            manifest["cases"][0]["unsupported"] = value
            with self.assertRaises(AuditError):
                validate_manifest(manifest)


if __name__ == "__main__":
    unittest.main()
