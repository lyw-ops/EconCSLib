"""Adversarial and regression coverage for evidence-hardened R001."""

from __future__ import annotations

import copy
import tempfile
import sys
import unittest
from pathlib import Path
from unittest import mock


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
RUBRIC_ROOT = SIDECAR_ROOT / "rubric"
SCRIPT_ROOT = RUBRIC_ROOT / "scripts"
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

import rubric_common  # noqa: E402
from compare_rubrics import comparison_errors, compare_rubrics  # noqa: E402
from r001_common import (  # noqa: E402
    DELTA_PATH,
    R001_PATH,
    child_from_parent_result,
    child_result_errors,
    compute_progress_vector,
    evidence_packet_errors,
    load_contracts,
    output_noise_errors,
)
from rubric_common import (  # noqa: E402
    R000_PATH,
    canonical_json_bytes,
    evaluate_shadow,
    load_json,
    sha256_bytes,
    sha256_file,
)
from validate_rubric import validate_rubric  # noqa: E402


REPORT_PATH = RUBRIC_ROOT / "reports" / "R001_PARENT_CHILD_REPLAY.json"


class RubricR001Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.parent, cls.child = load_contracts()
        cls.delta = load_json(DELTA_PATH)
        cls.report = load_json(REPORT_PATH)
        cls.child_results = (
            cls.report["child_accepted_results"]
            + cls.report["child_mutation_results"]
        )

    def test_r001_schema_and_static_comparison_pass(self) -> None:
        self.assertEqual(validate_rubric(R001_PATH)["status"], "passed")
        self.assertEqual(compare_rubrics()["status"], "passed")

    def test_parent_hash_mismatch_fails_closed(self) -> None:
        child = copy.deepcopy(self.child)
        child["parent_identity"]["canonical_sha256"] = "0" * 64
        with tempfile.TemporaryDirectory(prefix="eve-r001-parent-hash-") as raw:
            path = Path(raw) / "R001.json"
            path.write_bytes(canonical_json_bytes(child))
            with self.assertRaisesRegex(ValueError, "parent canonical hash mismatch"):
                load_contracts(child_path=path, require_child_detached_hash=False)

    def test_r000_canonical_bytes_and_hash_are_unchanged(self) -> None:
        self.assertEqual(
            sha256_bytes(canonical_json_bytes(self.parent)),
            "a8a2a9a70ffd8c744057dc7ad60393f3f5373e0cacb4b98d46a551302fadd719",
        )
        self.assertEqual(
            sha256_file(R000_PATH),
            "81615a8cb35dea8d557dee0a16ad6d3375418afaee76c812ab12694aeb4d4cdf",
        )
        self.assertTrue(self.report["invariants"]["r000_files_unchanged"])
        self.assertTrue(self.report["invariants"]["r000_replay_output_bytes_unchanged"])

    def _explicit_child(self) -> dict:
        child = copy.deepcopy(self.child)
        child["criteria"] = copy.deepcopy(self.parent["criteria"])
        return child

    def test_r000_criterion_deletion_or_rename_is_rejected(self) -> None:
        child = self._explicit_child()
        child["criteria"].pop()
        errors = comparison_errors(self.parent, child, self.delta)
        self.assertTrue(any("removed or renamed" in error for error in errors))

    def test_p1_fatal_hard_mirror_downgrade_is_rejected(self) -> None:
        child = self._explicit_child()
        criterion = next(
            item for item in child["criteria"]
            if item["criterion_id"] == "CORE.SOURCE_LOCK"
        )
        criterion["severity"] = "P2"
        criterion["score_role"] = "frontier"
        errors = comparison_errors(self.parent, child, self.delta)
        self.assertTrue(any("severity downgraded" in error for error in errors))
        self.assertTrue(any("fatal role downgraded" in error for error in errors))

    def test_prerequisite_removal_is_rejected(self) -> None:
        child = self._explicit_child()
        criterion = next(
            item for item in child["criteria"]
            if item["criterion_id"] == "CORE.SOURCE_LOCK"
        )
        criterion["prerequisites"].remove("CORE.EDIT_BOUNDARY")
        errors = comparison_errors(self.parent, child, self.delta)
        self.assertTrue(any("prerequisites removed" in error for error in errors))

    def test_criterion_dag_cycle_is_rejected(self) -> None:
        child = self._explicit_child()
        criterion = next(
            item for item in child["criteria"]
            if item["criterion_id"] == "CORE.PROTECTED_ASSETS_INITIAL"
        )
        criterion["prerequisites"] = ["CORE.AXIOM_ALLOWLIST"]
        errors = comparison_errors(self.parent, child, self.delta)
        self.assertTrue(any("DAG contains a cycle" in error for error in errors))

    def test_unregistered_criterion_delta_is_rejected(self) -> None:
        child = self._explicit_child()
        child["criteria"][0]["description"] += " undeclared"
        errors = comparison_errors(self.parent, child, self.delta)
        self.assertTrue(any("not exactly registered" in error for error in errors))

    def test_undeclared_prerequisite_override_is_rejected(self) -> None:
        child = copy.deepcopy(self.child)
        child["prerequisite_overrides"] = [
            {"criterion_id": "CORE.COMPILATION", "prerequisite_id": "CORE.ENVIRONMENT"}
        ]
        errors = comparison_errors(self.parent, child, self.delta)
        self.assertTrue(any("unregistered prerequisite override" in error for error in errors))

    def test_pass_missing_evidence_packet_fails_closed(self) -> None:
        result = copy.deepcopy(self.child_results[0])
        obligation = next(
            item for item in result["obligations"]
            if item["criterion_id"] == "CORE.COMPILATION"
        )
        del obligation["evidence_packet"]
        self.assertTrue(any("missing evidence packet" in error for error in child_result_errors(result, self.parent)))

    def test_evidence_hash_drift_is_rejected(self) -> None:
        result = copy.deepcopy(self.child_results[0])
        obligation = next(item for item in result["obligations"] if item["status"] == "PASS")
        obligation["evidence_packet"]["source_sha256"] = "0" * 64
        self.assertTrue(any("SHA-256 drift" in error for error in child_result_errors(result, self.parent)))

    def test_unknown_verifier_is_rejected(self) -> None:
        result = copy.deepcopy(self.child_results[0])
        obligation = next(item for item in result["obligations"] if item["status"] == "PASS")
        obligation["evidence_packet"]["verifier_id"] = "UNKNOWN.VERIFIER"
        self.assertTrue(any("unknown verifier" in error for error in child_result_errors(result, self.parent)))

    def test_syntactic_only_evidence_cannot_create_semantic_pass(self) -> None:
        result = copy.deepcopy(self.child_results[1])
        obligation = next(
            item for item in result["obligations"]
            if item["criterion_id"] == "TRANSPORT.ACTION_ENCODERS"
        )
        obligation["status"] = "PASS"
        obligation["evidence_packet"]["status"] = "PASS"
        obligation["evidence_packet"]["evidence_strength"] = "syntactic_only"
        errors = child_result_errors(result, self.parent)
        self.assertTrue(any("semantic PASS uses insufficient evidence" in error for error in errors))

    def test_review_only_evidence_neither_passes_nor_enters_vector(self) -> None:
        result = copy.deepcopy(self.child_results[0])
        before = result["shadow_progress_vector"]
        obligation = next(
            item for item in result["obligations"]
            if item["criterion_id"] == "PAIRED.SAME_MATHEMATICAL_TARGET"
        )
        obligation["status"] = "PASS"
        obligation["evidence_packet"]["status"] = "PASS"
        obligation["evidence_packet"]["evidence_strength"] = "review_only"
        after = compute_progress_vector(True, result["obligations"], self.parent)
        self.assertEqual(before, after)
        errors = child_result_errors(result, self.parent)
        self.assertTrue(any("review-only criterion cannot be PASS" in error for error in errors))

    def test_unknown_and_not_evaluated_do_not_increase_progress(self) -> None:
        baseline = copy.deepcopy(self.child_results[0])
        original = baseline["shadow_progress_vector"]
        for status in ("UNKNOWN", "NOT_EVALUATED"):
            with self.subTest(status=status):
                result = copy.deepcopy(baseline)
                obligation = next(
                    item for item in result["obligations"]
                    if item["criterion_id"] == "DIRECT.NASH_CHARACTERIZATION"
                )
                obligation["status"] = status
                obligation["evidence_packet"]["status"] = status
                vector = compute_progress_vector(True, result["obligations"], self.parent)
                self.assertLessEqual(
                    vector["lean_kernel_route_passes"],
                    original["lean_kernel_route_passes"],
                )

    def test_evidence_deletion_cannot_improve_progress(self) -> None:
        result = copy.deepcopy(self.child_results[0])
        original = result["shadow_progress_vector"]
        obligation = next(
            item for item in result["obligations"]
            if item["criterion_id"] == "CORE.COMPILATION"
        )
        del obligation["evidence_packet"]
        vector = compute_progress_vector(True, result["obligations"], self.parent)
        self.assertLessEqual(vector["core_frontier_passes"], original["core_frontier_passes"])

    def test_fatal_failure_sets_rank_eligible_false(self) -> None:
        fatal = next(
            result for result in self.report["child_mutation_results"]
            if result["candidate_id"] == "DIRECT-PREFIX-TAMPER"
        )
        self.assertFalse(fatal["shadow_progress_vector"]["fatal_integrity"])
        self.assertFalse(fatal["shadow_progress_vector"]["rank_eligible"])

    def test_hard_failure_never_receives_scalar_one(self) -> None:
        for result in self.report["child_mutation_results"]:
            with self.subTest(candidate=result["candidate_id"]):
                self.assertFalse(result["hard_oracle"]["hard_accepted"])
                self.assertNotEqual(result["shadow_search_score"], 1.0)

    def test_scalar_scores_are_byte_equal_for_all_fourteen_candidates(self) -> None:
        self.assertEqual(self.report["metrics"]["scalar_scores_byte_equal"], 14)
        self.assertTrue(all(item["scalar_score_bytes_equal"] for item in self.report["comparisons"]))

    def test_hard_decisions_and_failure_codes_are_preserved(self) -> None:
        self.assertEqual(self.report["metrics"]["hard_decisions_equal"], 14)
        self.assertEqual(self.report["metrics"]["failure_codes_equal"], 14)
        self.assertEqual(self.report["metrics"]["expected_failure_codes_preserved"], 12)

    def test_r001_conversion_is_byte_deterministic(self) -> None:
        parent_report = load_json(RUBRIC_ROOT / "reports" / "R000_STAGE2_REPLAY.json")
        parent_result = parent_report["accepted_results"][0]
        first = child_from_parent_result(parent_result, self.parent, self.child)
        second = child_from_parent_result(parent_result, self.parent, self.child)
        self.assertEqual(canonical_json_bytes(first), canonical_json_bytes(second))

    def test_wrapper_exception_remains_fail_closed(self) -> None:
        with mock.patch.object(
            rubric_common, "run_hard_oracle", side_effect=RuntimeError("test")
        ):
            parent_result = evaluate_shadow(
                "direct", Path("does-not-matter"), "R001-WRAPPER-ERROR"
            )
        child_result = child_from_parent_result(parent_result, self.parent, self.child)
        self.assertEqual(child_result["hard_oracle"]["status"], "error")
        self.assertFalse(child_result["hard_oracle"]["hard_accepted"])
        self.assertEqual(child_result["shadow_search_score"], 0.0)

    def test_replay_preserves_historical_assets_and_runtime(self) -> None:
        self.assertTrue(self.report["invariants"]["historical_assets_unchanged"])
        self.assertTrue(self.report["invariants"]["historical_runtime_unchanged"])

    def test_outputs_have_no_absolute_path_or_timestamp(self) -> None:
        self.assertEqual(output_noise_errors(self.report), [])

    def test_route_specific_criteria_are_not_applicable_on_other_route(self) -> None:
        direct = {item["criterion_id"]: item for item in self.child_results[0]["obligations"]}
        transport = {item["criterion_id"]: item for item in self.child_results[1]["obligations"]}
        self.assertEqual(direct["TRANSPORT.PAYOFF_PRESERVATION"]["status"], "NOT_APPLICABLE")
        self.assertEqual(transport["DIRECT.NASH_CHARACTERIZATION"]["status"], "NOT_APPLICABLE")

    def test_paired_unknown_is_not_upgraded(self) -> None:
        paired = {
            item["criterion_id"]: item
            for item in self.report["child_paired_obligations"]
        }
        self.assertEqual(paired["PAIRED.SAME_MATHEMATICAL_TARGET"]["status"], "UNKNOWN")
        self.assertEqual(paired["PAIRED.ROUTE_AGREEMENT"]["status"], "UNKNOWN")
        self.assertTrue(self.report["invariants"]["paired_unknown_not_upgraded"])

    def test_all_494_evidence_packets_validate(self) -> None:
        self.assertEqual(self.report["metrics"]["evidence_packets_validated"], 494)
        self.assertEqual(self.report["metrics"]["evidence_packet_validation_errors"], 0)
        for result in self.child_results:
            self.assertEqual(child_result_errors(result, self.parent), [])


if __name__ == "__main__":
    unittest.main()
