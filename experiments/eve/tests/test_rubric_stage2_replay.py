"""End-to-end public Stage 2 replay tests for R000."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_ROOT = SIDECAR_ROOT / "rubric" / "scripts"
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

from replay_stage2_public import replay, source_lock_obligation  # noqa: E402
from rubric_common import validate_obligation_results, validate_shadow_result  # noqa: E402


class RubricStage2ReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = replay(verify=True, write_reports=False)

    def test_two_accepted_candidates_remain_hard_accepted(self) -> None:
        self.assertEqual(self.report["metrics"]["accepted_candidates_evaluated"], 2)
        self.assertEqual(self.report["metrics"]["accepted_candidates_hard_accepted"], 2)
        by_id = {item["candidate_id"]: item for item in self.report["accepted_results"]}
        self.assertEqual(by_id["DIRECT-ACCEPTED"]["hard_oracle"]["score"], 1.0)
        self.assertEqual(by_id["TRANSPORT-ACCEPTED"]["hard_oracle"]["score"], 1.0)

    def test_all_twelve_mutations_remain_hard_rejected(self) -> None:
        self.assertEqual(self.report["metrics"]["mutations_evaluated"], 12)
        self.assertEqual(self.report["metrics"]["mutations_hard_rejected"], 12)
        self.assertTrue(all(
            item["hard_oracle"]["score"] == 0.0
            and not item["hard_oracle"]["hard_accepted"]
            for item in self.report["mutation_results"]
        ))

    def test_mutation_manifest_failure_codes_are_preserved(self) -> None:
        self.assertEqual(self.report["metrics"]["expected_failure_codes_preserved"], 12)
        self.assertEqual(self.report["metrics"]["expected_failure_codes_total"], 12)
        self.assertTrue(all(
            item["expected_failure_preserved"]
            for item in self.report["mutation_expectations"]
        ))

    def test_no_blocking_false_accepts(self) -> None:
        self.assertEqual(self.report["metrics"]["blocking_false_accepts"], 0)

    def test_replay_preserves_historical_assets(self) -> None:
        self.assertTrue(self.report["invariants"]["historical_assets_unchanged"])
        self.assertEqual(
            self.report["historical_asset_sha256_before"],
            self.report["historical_asset_sha256_after"],
        )

    def test_replay_does_not_write_historical_runtime(self) -> None:
        self.assertTrue(self.report["invariants"]["historical_runtime_unchanged"])

    def test_replay_has_zero_model_eve_and_quota_use(self) -> None:
        invariants = self.report["invariants"]
        self.assertEqual(invariants["model_calls"], 0)
        self.assertEqual(invariants["model_sessions"], 0)
        self.assertEqual(invariants["quota_consumed_by_this_task"], 0)
        self.assertEqual(invariants["eve_execute_invocations"], 0)

    def test_paired_review_only_claim_is_not_machine_passed(self) -> None:
        paired = {item["criterion_id"]: item for item in self.report["paired_obligations"]}
        self.assertEqual(paired["PAIRED.SAME_SOURCE_LOCK"]["status"], "PASS")
        self.assertEqual(paired["PAIRED.SAME_MATHEMATICAL_TARGET"]["status"], "UNKNOWN")
        self.assertEqual(paired["PAIRED.INDEPENDENT_WORKSPACES"]["status"], "PASS")
        self.assertEqual(paired["PAIRED.ROUTE_AGREEMENT"]["status"], "UNKNOWN")

    def test_source_lock_evidence_is_machine_checked_and_concrete(self) -> None:
        paired = {item["criterion_id"]: item for item in self.report["paired_obligations"]}
        result = paired["PAIRED.SAME_SOURCE_LOCK"]
        self.assertTrue(any(
            item.startswith("direct-case:source_lock.id=")
            for item in result["evidence"]
        ))
        self.assertTrue(any(
            item.startswith("transport-case:source_lock.id=")
            for item in result["evidence"]
        ))
        self.assertTrue(any(
            item.startswith("source-lock:file-sha256=")
            for item in result["evidence"]
        ))
        self.assertTrue(all(not item.startswith("/") for item in result["evidence"]))

    def test_source_lock_mismatch_fails_and_missing_field_is_unknown(self) -> None:
        def case(sha256: str) -> dict:
            return {
                "source_lock": {
                    "id": "LOCK",
                    "path": "tracked-source.json",
                    "sha256": sha256,
                }
            }

        mismatch = source_lock_obligation(case("a" * 64), case("b" * 64))
        self.assertEqual(mismatch["status"], "FAIL")
        missing = case("a" * 64)
        del missing["source_lock"]["sha256"]
        self.assertEqual(
            source_lock_obligation(missing, case("a" * 64))["status"],
            "UNKNOWN",
        )

    def test_all_replay_shadow_and_obligation_outputs_match_schemas(self) -> None:
        for result in self.report["accepted_results"] + self.report["mutation_results"]:
            validate_shadow_result(result)
            validate_obligation_results(result["obligations"])
        validate_obligation_results(self.report["paired_obligations"])


if __name__ == "__main__":
    unittest.main()
