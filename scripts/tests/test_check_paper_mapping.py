"""Inventory rejection tests; these do not execute or certify Verus proofs."""
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("paper_mapping", ROOT / "scripts/check-paper-mapping.py")
mapping = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mapping)


class InventoryValidation(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.base = json.loads((ROOT / mapping.INVENTORY).read_text())
        cls.ledger = json.loads((ROOT / mapping.LEDGER).read_text())
        cls.plan = json.loads((ROOT / mapping.PLAN).read_text())

    def validate(self, data, check_inputs=False):
        mapping.validate(data, self.ledger, self.plan, root=ROOT, check_inputs=check_inputs)

    def rejected(self, change, expected):
        data = deepcopy(self.base)
        change(data)
        with self.assertRaisesRegex(ValueError, expected):
            self.validate(data)

    def test_inventory_keeps_all_original_entries_and_surfaces(self):
        self.validate(self.base)

    def test_missing_original_entry_is_rejected(self):
        self.rejected(lambda d: d["items"].pop(), "Every numbered")

    def test_false_completion_claim_is_rejected(self):
        self.rejected(lambda d: d["completionClaims"].update(implementationMappingComplete=True),
                      "must not claim")

    def test_missing_global_obligation_is_rejected(self):
        self.rejected(lambda d: d["integration"].pop(), "All four")

    def test_unnumbered_async_scope_cannot_disappear(self):
        self.rejected(lambda d: d["surfaces"].__setitem__(
            slice(None), [s for s in d["surfaces"] if s["id"] != "async"]), "all eight")

    def test_delivery_only_coverage_cannot_hide_semantic_gap(self):
        def remove_substantive_coverage(d):
            for task in d["obligations"]:
                if not task["id"].startswith("D") and 28 in task["paperItems"]:
                    task["paperItems"].remove(28)
            d["items"][27]["obligations"] = ["D01", "D02"]
        self.rejected(remove_substantive_coverage, "substantive obligations")

    def test_reverse_allocation_cannot_drift(self):
        self.rejected(lambda d: d["items"][0]["obligations"].append("R01"),
                      "exact substantive obligations")

    def test_circular_closure_prerequisite_is_rejected(self):
        self.rejected(lambda d: d["obligations"][0]["dependsOn"].append("R08"),
                      "Cyclic closure dependency")

    def test_target_state_proof_cannot_become_environment_assumption(self):
        self.rejected(lambda d: d["premises"][3].update(kind="environment"),
                      "cannot become environment")

    def test_closed_label_without_evidence_is_rejected(self):
        self.rejected(lambda d: d["obligations"][0].update(status="closed"),
                      "Closure requires")

    def test_old_artifact_hash_alone_cannot_close_an_obligation(self):
        def old_evidence(d):
            path = "docs/r1-semantics.md"
            d["obligations"][0].update(status="closed", closureEvidence=[
                {"kind": k, "file": path, "sha256": hashlib.sha256((ROOT / path).read_bytes()).hexdigest()}
                for k in ("proof", "caller-review", "reproduction")
            ])
        self.rejected(old_evidence, "not bound to the current review inputs")

    def test_fictitious_review_symbol_is_rejected(self):
        self.rejected(lambda d: d["obligations"][0]["review"][0].update(
            symbol="invented_complete_whole_paper_proof"), "Missing review symbol")

    def test_source_fingerprint_cannot_be_omitted(self):
        self.rejected(lambda d: d["reviewInputSha256"].pop("docs/paper-obligations.json"),
                      "fingerprint must cover exactly")

    def test_stale_input_cannot_be_reused_as_current_review(self):
        data = deepcopy(self.base)
        data["reviewInputSha256"]["docs/paper-obligations.json"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Review input changed"):
            self.validate(data, check_inputs=True)

    def test_r3_recovery_and_deletion_are_not_dropped(self):
        self.rejected(lambda d: d["r3Packages"][-1]["obligations"].remove("R09"),
                      "Retain all fixed R3")

    def test_views_derive_original_statuses_instead_of_overriding_them(self):
        ledger = deepcopy(self.ledger)
        ledger["items"][61]["status"] = "partial"
        for lang in mapping.VIEWS:
            rendered = mapping.render(self.base, ledger, self.plan, lang)
            row = next(line for line in rendered.splitlines() if line.startswith("| Lemma 62:"))
            self.assertIn("`partial`", row)
            self.assertNotIn("`proved`", row)

    def test_bilingual_review_text_is_required(self):
        self.rejected(lambda d: d["obligations"][0]["remaining"].pop("zh-CN"),
                      "Missing bilingual")


if __name__ == "__main__":
    unittest.main()
