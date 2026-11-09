"""Regressions for gaps and evidence that must not be silently dropped."""

import copy
import unittest
import tomllib

from instruction_inventory import ROOT, parser_spellings, probe_source, validate_inventory
from proof_audit import AuditError


class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / "src/parser.rs").read_text()
        self.data = tomllib.loads((ROOT / "instructions.toml").read_text())

    def test_real_inventory_covers_dispatch_spellings(self):
        validate_inventory(self.data, self.source)

    def test_nested_matches_comments_and_string_braces_are_not_dispatch_forms(self):
        source = '''let instr = match op.as_str() {
          "a" | "b" => { let x = "}"; match op.as_str() { "nested" => x } },
          // "comment" => {}
          "c" => value("{"),
          _ => error("unsupported"),
        };'''
        self.assertEqual(parser_spellings(source), {"a", "b", "c"})
        with self.assertRaises(AuditError):
            parser_spellings(source.removesuffix("};"))

    def test_missing_or_duplicate_form_fails(self):
        for duplicate in (False, True):
            data = copy.deepcopy(self.data)
            if duplicate:
                data["forms"].append(data["forms"][0])
            else:
                data["forms"].pop()
            with self.subTest(duplicate=duplicate), self.assertRaises(AuditError):
                validate_inventory(data, self.source)

    def test_paper_correspondence_cannot_be_inferred_from_local_counts(self):
        for mutation in ("paper", "form", "count"):
            data = copy.deepcopy(self.data)
            if mutation == "paper":
                data["paper"]["mapping_status"] = "covered"
            elif mutation == "form":
                data["forms"][0]["paper_mapping"] = "covered"
            else:
                data["paper"]["forms"] = len(data["forms"])
            with self.subTest(mutation=mutation), self.assertRaises(AuditError):
                validate_inventory(data, self.source)

    def test_wrong_probe_missing_evidence_and_alias_cycles_fail(self):
        for mutation in ("probe", "semantics", "regression", "alias"):
            data = copy.deepcopy(self.data)
            entry = data["forms"][0]
            if mutation == "probe":
                entry["instruction"] = "ret;"
            elif mutation == "semantics":
                entry["semantics"] = "lean/Missing.lean"
            elif mutation == "regression":
                entry["regression"] = "missing_rust_regression"
            else:
                other = data["forms"][1]
                entry["canonical"], other["canonical"] = other["opcode"], entry["opcode"]
            with self.subTest(mutation=mutation), self.assertRaises(AuditError):
                validate_inventory(data, self.source)

    def test_unknown_qualifier_probe_changes_only_the_opcode(self):
        entry = self.data["forms"][0]
        profile = self.data["profiles"][entry["profile"]]
        positive = probe_source(entry, profile, 0)
        negative = probe_source(entry, profile, 0, negative=True)
        self.assertEqual(negative.replace(".ptx_verify_unmodeled", ""), positive)
        self.assertEqual(negative.count(".ptx_verify_unmodeled"), 1)


if __name__ == "__main__":
    unittest.main()
