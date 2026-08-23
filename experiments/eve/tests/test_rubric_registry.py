"""Registry, schema, detached-hash, and obligation-graph tests for R000."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
RUBRIC_ROOT = SIDECAR_ROOT / "rubric"
SCRIPT_ROOT = RUBRIC_ROOT / "scripts"
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

from rubric_common import (  # noqa: E402
    R000_PATH,
    REPO_ROOT,
    canonical_json_bytes,
    load_json,
    sha256_bytes,
    sha256_file,
    validate_instance,
)
from validate_rubric import validate_rubric  # noqa: E402


class RubricRegistryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.rubric = load_json(R000_PATH)
        cls.criteria = cls.rubric["criteria"]

    def test_r000_passes_schema_and_graph_validation(self) -> None:
        report = validate_rubric()
        self.assertEqual(report["status"], "passed", report)
        self.assertEqual(report["criteria"], 35)
        self.assertEqual(report["graphs"], 4)

    def test_criterion_ids_are_unique(self) -> None:
        identifiers = [item["criterion_id"] for item in self.criteria]
        self.assertEqual(len(identifiers), len(set(identifiers)))

    def test_every_prerequisite_exists(self) -> None:
        identifiers = {item["criterion_id"] for item in self.criteria}
        for criterion in self.criteria:
            with self.subTest(criterion=criterion["criterion_id"]):
                self.assertLessEqual(set(criterion["prerequisites"]), identifiers)

    def test_all_four_obligation_graphs_are_present_and_acyclic(self) -> None:
        for name in ("core", "direct", "transport", "paired"):
            with self.subTest(graph=name):
                graph = load_json(RUBRIC_ROOT / "obligation_graphs" / f"{name}.json")
                self.assertEqual(graph["scope"], name if name != "core" else "all")
        self.assertNotIn("cycle", " ".join(validate_rubric()["errors"]))

    def test_detached_hash_matches_normalized_r000(self) -> None:
        recorded = (RUBRIC_ROOT / "versions" / "R000.sha256").read_text().split()[0]
        actual = sha256_bytes(canonical_json_bytes(self.rubric))
        self.assertEqual(recorded, actual)

    def test_historical_artifact_hashes_match_registry(self) -> None:
        for source in self.rubric["artifact_sources"]:
            with self.subTest(path=source["path"]):
                self.assertEqual(sha256_file(REPO_ROOT / source["path"]), source["sha256"])

    def test_hard_evaluator_source_hash_is_frozen(self) -> None:
        sources = {item["path"]: item["sha256"] for item in self.rubric["artifact_sources"]}
        path = "experiments/eve/scripts/evaluate_stage2_entry_game.py"
        self.assertEqual(
            sources[path],
            "7dd10441541593ea63d9de70595b786e130a67327a33c8d6cf4c91d63d6c256f",
        )

    def test_review_only_and_syntactic_evidence_are_not_frontier_scores(self) -> None:
        for criterion in self.criteria:
            with self.subTest(criterion=criterion["criterion_id"]):
                if criterion["kind"] == "review_only":
                    self.assertEqual(criterion["score_role"], "diagnostic_only")
                if criterion["evidence_strength"] == "syntactic_only" and criterion["kind"] == "semantic_progress":
                    self.assertEqual(criterion["score_role"], "diagnostic_only")

    def test_obligation_result_schema_accepts_all_five_statuses(self) -> None:
        schema = load_json(RUBRIC_ROOT / "schemas" / "obligation-result.schema.json")
        for status in ("PASS", "FAIL", "NOT_EVALUATED", "NOT_APPLICABLE", "UNKNOWN"):
            with self.subTest(status=status):
                errors = validate_instance({
                    "criterion_id": "CORE.COMPILATION",
                    "status": status,
                    "evidence": [],
                    "rationale": "test",
                }, schema)
                self.assertEqual(errors, [])


if __name__ == "__main__":
    unittest.main()
