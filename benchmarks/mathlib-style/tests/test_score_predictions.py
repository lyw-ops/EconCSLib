from __future__ import annotations

import sys
import unittest
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))

from phase4_harness import schema_validators  # noqa: E402
from score_predictions import finding_metrics, findings_f1, score_all, score_one  # noqa: E402


def finding(rule: str = "FMT-008", artifact: str = "A", start: int = 1, end: int = 1):
    return {
        "finding_id": "f1",
        "rule_id": rule,
        "role": "primary",
        "rule_strength": "SHOULD",
        "review_priority": "MINOR",
        "span": {
            "artifact": artifact,
            "declaration_name": None,
            "syntax_kind": None,
            "start": {"line": start, "column": 1},
            "end": {"line": end, "column": 20},
        },
        "evidence": ["pinned rule"],
        "rationale": "test rationale",
    }


def common_prediction(case_id: str, task: str, findings=None):
    return {
        "schema_version": "0.3.0",
        "case_id": case_id,
        "task": task,
        "answerability": "ANSWERABLE",
        "confidence": "HIGH",
        "findings": findings or [],
        "missing_context": [],
        "rationale": "test",
    }


class ScorerTests(unittest.TestCase):
    def test_pair_correct_wrong_and_tie(self):
        gold = {
            "case_id": "abc", "task": "PAIR", "answerability": "ANSWERABLE",
            "verdict": "TIE", "accepted_verdicts": ["TIE"], "findings": [],
        }
        correct = common_prediction("abc", "PAIR") | {"verdict": "TIE"}
        wrong = common_prediction("abc", "PAIR") | {"verdict": "A"}
        self.assertEqual(score_one(correct, gold)["score"], 1.0)
        self.assertLess(score_one(wrong, gold)["score"], 1.0)

    def test_multiple_acceptable_pair(self):
        gold = {
            "case_id": "abc", "task": "PAIR", "answerability": "MULTIPLE_ACCEPTABLE",
            "verdict": "TIE", "accepted_verdicts": ["A", "TIE"], "findings": [],
        }
        prediction = common_prediction("abc", "PAIR") | {
            "answerability": "MULTIPLE_ACCEPTABLE", "verdict": "A"
        }
        self.assertEqual(score_one(prediction, gold)["score"], 1.0)

    def test_insufficient_context(self):
        gold = {
            "case_id": "abc", "task": "DETECT",
            "answerability": "INSUFFICIENT_CONTEXT", "findings": [],
        }
        prediction = common_prediction("abc", "DETECT") | {
            "answerability": "INSUFFICIENT_CONTEXT", "missing_context": ["surrounding proof"]
        }
        self.assertEqual(score_one(prediction, gold)["score"], 1.0)

    def test_empty_finding_false_positive(self):
        self.assertEqual(findings_f1([], []), 1.0)
        self.assertEqual(findings_f1([finding()], []), 0.0)

    def test_partial_span_receives_partial_credit(self):
        partial = findings_f1([finding(start=2, end=3)], [finding(start=1, end=3)])
        self.assertGreater(partial, 0.0)
        self.assertLess(partial, 1.0)

    def test_detect_precision_recall_and_priority_are_separate(self):
        predicted = [finding(), finding(rule="PRF-001")]
        predicted[0]["review_priority"] = "BLOCKING"
        result = finding_metrics(predicted, [finding()])
        self.assertLess(result["precision"], 1.0)
        self.assertEqual(result["recall"], 1.0)
        self.assertEqual(result["priority_accuracy"], 0.0)
        self.assertEqual(result["unmatched_predictions"], 1)

    def test_repair_gate(self):
        gold = {
            "case_id": "abc", "task": "REPAIR", "answerability": "ANSWERABLE",
            "findings": [], "reference_repairs": ["theorem x : True := by trivial"],
        }
        correct = common_prediction("abc", "REPAIR") | {
            "repaired_code": "theorem x : True := by trivial"
        }
        wrong = common_prediction("abc", "REPAIR") | {"repaired_code": "theorem x : True := by sorry"}
        evaluation = {
            "candidate_sha256": __import__("hashlib").sha256(
                correct["repaired_code"].encode()
            ).hexdigest(),
            "accepted": True,
            "gates": {"compile": True},
            "edit_cost": {"changed_lines": 1, "changed_tokens": 1},
            "reference_text_match_diagnostic_only": False,
        }
        self.assertEqual(score_one(correct, gold, evaluation)["score"], 1.0)
        rejected = evaluation | {
            "candidate_sha256": __import__("hashlib").sha256(
                wrong["repaired_code"].encode()
            ).hexdigest(),
            "accepted": False,
        }
        self.assertLess(score_one(wrong, gold, rejected)["score"], 1.0)

    def test_repair_reference_text_is_diagnostic_only(self):
        gold = {
            "case_id": "abc", "task": "REPAIR", "answerability": "ANSWERABLE",
            "findings": [], "reference_repairs": ["reference text"],
        }
        prediction = common_prediction("abc", "REPAIR") | {"repaired_code": "different valid text"}
        evaluation = {
            "candidate_sha256": __import__("hashlib").sha256(
                prediction["repaired_code"].encode()
            ).hexdigest(),
            "accepted": True,
            "gates": {"all": True},
            "edit_cost": {"changed_lines": 1, "changed_tokens": 2},
            "reference_text_match_diagnostic_only": False,
        }
        self.assertEqual(score_one(prediction, gold, evaluation)["score"], 1.0)

    def test_locate_preferred_and_accepted(self):
        gold = {
            "case_id": "abc", "task": "LOCATE", "answerability": "MULTIPLE_ACCEPTABLE",
            "findings": [], "preferred_location_ids": ["loc_a"],
            "accepted_location_ids": ["loc_a", "loc_b"],
        }
        prediction = common_prediction("abc", "LOCATE") | {
            "answerability": "MULTIPLE_ACCEPTABLE", "location_ids": ["loc_a", "loc_b"]
        }
        self.assertEqual(score_one(prediction, gold)["score"], 1.0)

    def test_invalid_prediction_rejected_by_schema(self):
        validator = schema_validators()["prediction.schema.json"]
        invalid = {"schema_version": "0.3.0", "case_id": "abc", "task": "PAIR"}
        self.assertTrue(list(validator.iter_errors(invalid)))

    def test_primary_metrics_exclude_mirrors_and_report_global_metrics(self):
        gold = {
            "msb_p001": {
                "case_id": "msb_p001", "task": "PAIR", "answerability": "ANSWERABLE",
                "verdict": "TIE", "accepted_verdicts": ["TIE"], "findings": [],
            },
            "msb_p001_mirror": {
                "case_id": "msb_p001_mirror", "task": "PAIR",
                "answerability": "ANSWERABLE", "verdict": "TIE",
                "accepted_verdicts": ["TIE"], "findings": [],
            },
        }
        predictions = {
            case_id: common_prediction(case_id, "PAIR") | {"verdict": "TIE"}
            for case_id in gold
        }
        report = score_all(predictions, gold)
        self.assertEqual(report["primary_case_count"], 1)
        self.assertEqual(report["evaluated_case_count_including_mirrors"], 2)
        self.assertEqual(report["global_metrics"]["answerability_accuracy"], 1.0)
        self.assertIn("abstention_calibration", report["global_metrics"])
        self.assertIn("unsupported_rationale_rate", report["global_metrics"])


if __name__ == "__main__":
    unittest.main()
