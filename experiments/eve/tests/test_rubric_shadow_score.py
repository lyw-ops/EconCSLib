"""Fail-fast mapping and monotone shadow-score tests for R000."""

from __future__ import annotations

import tempfile
import sys
import unittest
from pathlib import Path
from unittest import mock


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_ROOT = SIDECAR_ROOT / "rubric" / "scripts"
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

import replay_stage2_public  # noqa: E402
import rubric_common  # noqa: E402
from rubric_common import (  # noqa: E402
    CRITERION_GATE,
    FRONTIER_CRITERIA,
    R000_PATH,
    canonical_json_bytes,
    compute_shadow_score,
    evaluate_shadow,
    finalize_shadow_result,
    load_json,
    map_obligations,
    prerequisite_consistency_errors,
    propagate_prerequisite_status,
    validate_shadow_result,
)


def synthetic_report(failure_code: str, failure_criterion: str) -> dict:
    gates = {gate: False for gate in CRITERION_GATE.values()}
    failure_stage = rubric_common.CORE_STAGE[failure_criterion]
    for criterion_id, stage in rubric_common.CORE_STAGE.items():
        gate = CRITERION_GATE.get(criterion_id)
        if gate is not None and stage < failure_stage:
            gates[gate] = True
    if failure_stage == 5:
        gates["static_guard"] = failure_criterion != "CORE.NO_PLACEHOLDER"
        gates["trusted_bypass_guard"] = failure_criterion != "CORE.NO_TRUSTED_BYPASS"
    gates["protected_assets_final"] = True
    return {
        "status": "failed",
        "score": 0.0,
        "gates": gates,
        "failure_codes": [failure_code],
    }


class RubricShadowScoreTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.rubric = load_json(R000_PATH)

    def test_trust_task_and_route_identity_failures_score_zero(self) -> None:
        cases = (
            ("protected-task-prefix-changed", "CORE.TASK_IDENTITY"),
            ("forbidden-construct", "CORE.NO_PLACEHOLDER"),
            ("trusted-bypass", "CORE.NO_TRUSTED_BYPASS"),
            ("route-discipline-violation", "CORE.ROUTE_IDENTITY"),
        )
        for code, criterion in cases:
            with self.subTest(code=code):
                obligations = map_obligations(
                    synthetic_report(code, criterion), self.rubric, "direct"
                )
                self.assertEqual(compute_shadow_score(False, obligations), 0.0)

    def test_ordinary_rejected_frontier_is_positive_and_capped(self) -> None:
        report = synthetic_report(
            "target-declaration-missing-or-wrong-type", "CORE.TARGET_DECLARATIONS"
        )
        obligations = map_obligations(report, self.rubric, "direct")
        score = compute_shadow_score(False, obligations)
        self.assertGreater(score, 0.0)
        self.assertLessEqual(score, 0.95)

    def test_hard_accepted_score_is_exactly_one(self) -> None:
        obligations = [
            {"criterion_id": item, "status": "UNKNOWN"} for item in FRONTIER_CRITERIA
        ]
        self.assertEqual(compute_shadow_score(True, obligations), 1.0)

    def test_unknown_and_not_evaluated_never_count_as_pass(self) -> None:
        base = [
            {"criterion_id": item, "status": "UNKNOWN"} for item in FRONTIER_CRITERIA
        ]
        unknown_score = compute_shadow_score(False, base)
        not_evaluated = [dict(item, status="NOT_EVALUATED") for item in base]
        self.assertEqual(compute_shadow_score(False, not_evaluated), unknown_score)
        one_pass = [dict(item) for item in base]
        one_pass[0]["status"] = "PASS"
        self.assertGreaterEqual(compute_shadow_score(False, one_pass), unknown_score)

    def test_more_reliable_passes_do_not_reduce_score(self) -> None:
        obligations = [
            {"criterion_id": item, "status": "UNKNOWN"} for item in FRONTIER_CRITERIA
        ]
        scores = []
        for index in range(len(obligations)):
            obligations[index]["status"] = "PASS"
            scores.append(compute_shadow_score(False, obligations))
        self.assertEqual(scores, sorted(scores))
        self.assertLessEqual(scores[-1], 0.95)

    def test_fail_fast_false_gates_after_frontier_are_not_evaluated(self) -> None:
        report = synthetic_report("route-discipline-violation", "CORE.ROUTE_IDENTITY")
        obligations = {
            item["criterion_id"]: item for item in map_obligations(report, self.rubric, "direct")
        }
        self.assertEqual(obligations["CORE.ROUTE_IDENTITY"]["status"], "FAIL")
        self.assertEqual(obligations["CORE.ENVIRONMENT"]["status"], "NOT_EVALUATED")
        self.assertEqual(obligations["CORE.COMPILATION"]["status"], "NOT_EVALUATED")
        self.assertEqual(obligations["CORE.PROTECTED_ASSETS_FINAL"]["status"], "PASS")

    def test_case_contract_failure_does_not_mislabel_boundary_false(self) -> None:
        report = synthetic_report("case-route-invalid", "CORE.SOURCE_LOCK")
        # The legacy evaluator aggregates case and boundary checks before it
        # sets gates.boundary, so that false value is not a boundary failure.
        report["gates"]["boundary"] = False
        obligations = {
            item["criterion_id"]: item for item in map_obligations(report, self.rubric, "direct")
        }
        self.assertEqual(obligations["CORE.SOURCE_LOCK"]["status"], "FAIL")
        self.assertEqual(obligations["CORE.EDIT_BOUNDARY"]["status"], "PASS")
        self.assertEqual(obligations["CORE.IMPORT_BOUNDARY"]["status"], "NOT_EVALUATED")

    def test_candidate_size_failure_occurs_after_source_identity(self) -> None:
        report = synthetic_report("candidate-too-large", "CORE.EDIT_BOUNDARY")
        report["gates"]["boundary"] = True
        obligations = {
            item["criterion_id"]: item for item in map_obligations(report, self.rubric, "direct")
        }
        self.assertEqual(obligations["CORE.EDIT_BOUNDARY"]["status"], "FAIL")
        self.assertEqual(obligations["CORE.SOURCE_LOCK"]["status"], "UNKNOWN")
        self.assertEqual(obligations["CORE.IMPORT_BOUNDARY"]["status"], "NOT_EVALUATED")

    def test_strict_prerequisite_status_propagation(self) -> None:
        criterion = {"criterion_id": "B", "prerequisites": ["A"]}
        direct_pass = {
            "criterion_id": "B",
            "status": "PASS",
            "evidence": ["direct:B"],
            "rationale": "Direct evidence passes.",
        }
        for status in ("UNKNOWN", "NOT_EVALUATED", "FAIL"):
            with self.subTest(status=status):
                prerequisite = {
                    "criterion_id": "A",
                    "status": status,
                    "evidence": [],
                    "rationale": "test",
                }
                propagated = propagate_prerequisite_status(
                    criterion, {"A": prerequisite}, direct_pass
                )
                self.assertNotEqual(propagated["status"], "PASS")
        prerequisite_pass = {
            "criterion_id": "A",
            "status": "PASS",
            "evidence": ["direct:A"],
            "rationale": "Direct evidence passes.",
        }
        self.assertEqual(
            propagate_prerequisite_status(
                criterion, {"A": prerequisite_pass}, direct_pass
            )["status"],
            "PASS",
        )

    def test_runtime_invariant_detects_dependent_pass(self) -> None:
        rubric = {
            "criteria": [
                {"criterion_id": "A", "prerequisites": []},
                {"criterion_id": "B", "prerequisites": ["A"]},
            ]
        }
        results = [
            {"criterion_id": "A", "status": "UNKNOWN"},
            {"criterion_id": "B", "status": "PASS"},
        ]
        self.assertEqual(len(prerequisite_consistency_errors(rubric, results)), 1)

    def test_route_specific_criteria_are_not_applicable_on_other_route(self) -> None:
        report = synthetic_report("compile-failed", "CORE.COMPILATION")
        direct = {item["criterion_id"]: item for item in map_obligations(report, self.rubric, "direct")}
        transport = {item["criterion_id"]: item for item in map_obligations(report, self.rubric, "transport")}
        self.assertEqual(direct["TRANSPORT.PAYOFF_PRESERVATION"]["status"], "NOT_APPLICABLE")
        self.assertEqual(transport["DIRECT.NASH_CHARACTERIZATION"]["status"], "NOT_APPLICABLE")

    def test_syntactic_transport_evidence_remains_unknown(self) -> None:
        gates = {gate: True for gate in CRITERION_GATE.values()}
        report = {"status": "passed", "score": 1.0, "gates": gates, "failure_codes": []}
        obligations = {item["criterion_id"]: item for item in map_obligations(report, self.rubric, "transport")}
        self.assertEqual(obligations["TRANSPORT.CERTIFICATE_CONSUMED"]["status"], "UNKNOWN")
        self.assertEqual(obligations["TRANSPORT.GENERAL_NASH_THEOREM_APPLICATION"]["status"], "UNKNOWN")

    def test_wrapper_exception_fails_closed(self) -> None:
        with mock.patch.object(rubric_common, "run_hard_oracle", side_effect=RuntimeError("test")):
            result = evaluate_shadow("direct", Path("does-not-matter"), "WRAPPER-ERROR")
        self.assertEqual(result["hard_oracle"]["status"], "error")
        self.assertFalse(result["hard_oracle"]["hard_accepted"])
        self.assertEqual(result["shadow_search_score"], 0.0)
        validate_shadow_result(result)

    def test_all_shadow_output_classes_are_schema_valid(self) -> None:
        accepted = {
            "status": "passed",
            "score": 1.0,
            "gates": {gate: True for gate in CRITERION_GATE.values()},
            "failure_codes": [],
        }
        cases = (
            ("direct", accepted),
            ("transport", accepted),
            (
                "direct",
                synthetic_report(
                    "target-declaration-missing-or-wrong-type",
                    "CORE.TARGET_DECLARATIONS",
                ),
            ),
            (
                "direct",
                synthetic_report(
                    "protected-task-prefix-changed", "CORE.TASK_IDENTITY"
                ),
            ),
        )
        for index, (route, report) in enumerate(cases):
            with self.subTest(route=route, index=index):
                with mock.patch.object(
                    rubric_common,
                    "run_hard_oracle",
                    return_value=(report, "a" * 64),
                ):
                    result = evaluate_shadow(
                        route, Path("does-not-matter"), f"SCHEMA-{index}"
                    )
                validate_shadow_result(result)

    def test_invalid_shadow_output_fails_closed(self) -> None:
        accepted = {
            "status": "passed",
            "score": 1.0,
            "gates": {gate: True for gate in CRITERION_GATE.values()},
            "failure_codes": [],
        }
        with mock.patch.object(
            rubric_common,
            "run_hard_oracle",
            return_value=(accepted, "b" * 64),
        ):
            result = evaluate_shadow(
                "direct", Path("does-not-matter"), "SCHEMA-INVALID"
            )
        invalid = dict(result, shadow_search_score=1.2)
        with self.assertRaises(ValueError):
            validate_shadow_result(invalid)
        failed_closed = finalize_shadow_result(invalid, self.rubric)
        validate_shadow_result(failed_closed)
        self.assertEqual(failed_closed["hard_oracle"]["status"], "error")
        self.assertFalse(failed_closed["hard_oracle"]["hard_accepted"])
        self.assertEqual(failed_closed["shadow_search_score"], 0.0)
        self.assertIn(
            "shadow-output-schema-invalid",
            failed_closed["hard_oracle"]["failure_codes"],
        )

    def test_real_shadow_output_is_byte_deterministic(self) -> None:
        with tempfile.TemporaryDirectory(prefix="eve-rubric-determinism-") as raw_temp:
            root = Path(raw_temp)
            candidate = replay_stage2_public.materialize_candidate(
                "direct", "accepted", [], root, "DIRECT-ACCEPTED"
            )
            first = evaluate_shadow("direct", candidate, "DIRECT-ACCEPTED")
            second = evaluate_shadow("direct", candidate, "DIRECT-ACCEPTED")
        self.assertEqual(canonical_json_bytes(first), canonical_json_bytes(second))
        self.assertEqual(first["hard_oracle"]["score"], 1.0)
        self.assertEqual(first["shadow_search_score"], 1.0)


if __name__ == "__main__":
    unittest.main()
