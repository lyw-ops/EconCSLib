"""Acceptance, mutation, and pair checks for the Stage 2 Entry Game task."""

from __future__ import annotations

import importlib.util
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
TASK_ROOT = SIDECAR_ROOT / "stage2_entry_game"


def _load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


EVALUATOR = _load_module(
    "eve_stage2_entry_evaluator",
    SIDECAR_ROOT / "scripts" / "evaluate_stage2_entry_game.py",
)
PAIR = _load_module(
    "eve_stage2_pair_evaluator",
    SIDECAR_ROOT / "scripts" / "evaluate_stage2_pair.py",
)


def _apply_operations(source: str, route: str, operations: list[dict]) -> str:
    marker = f"/-! ## Solver declarations: {route} route -/"
    result = source
    for operation in operations:
        kind = operation["kind"]
        if kind == "prepend":
            result = operation["text"] + result
        elif kind == "insert_after_marker":
            if result.count(marker) != 1:
                raise AssertionError("mutation marker is not unique")
            result = result.replace(marker, marker + operation["text"], 1)
        elif kind == "replace_once":
            old = operation["old"]
            if result.count(old) != 1:
                raise AssertionError(f"replace_once source is not unique: {old}")
            result = result.replace(old, operation["new"], 1)
        elif kind == "replace_all":
            old = operation["old"]
            if old not in result:
                raise AssertionError(f"replace_all source is absent: {old}")
            result = result.replace(old, operation["new"])
        else:
            raise AssertionError(f"unknown mutation operation: {kind}")
    return result


class Stage2EntryGameTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.mutations = json.loads(
            (TASK_ROOT / "mutations.json").read_text(encoding="utf-8")
        )["mutations"]

    def materialize(
        self, route: str, base: str, operations: list[dict], root: Path,
        *, label: str | None = None,
    ) -> Path:
        candidate = root / (label or f"{route}-{base}")
        shutil.copytree(TASK_ROOT / route / "seed", candidate)
        source_path = (
            TASK_ROOT / route / "seed" / "Candidate.lean"
            if base == "seed"
            else TASK_ROOT / route / "expected" / "Accepted.lean"
        )
        source = _apply_operations(
            source_path.read_text(encoding="utf-8"), route, operations
        )
        (candidate / "Candidate.lean").write_text(source, encoding="utf-8")
        return candidate

    def test_accepted_fixtures_pass_every_gate(self) -> None:
        with tempfile.TemporaryDirectory(prefix="eve-stage2-accepted-") as raw_temp:
            root = Path(raw_temp)
            for route in ("direct", "transport"):
                with self.subTest(route=route):
                    candidate = self.materialize(route, "accepted", [], root)
                    report = EVALUATOR.evaluate_candidate(route, candidate)
                    self.assertEqual(report["status"], "passed", report)
                    self.assertEqual(report["score"], 1.0)
                    self.assertTrue(all(report["gates"].values()))
                    self.assertEqual(
                        report["axioms"]["observed"], EVALUATOR.ALLOWED_AXIOMS
                    )

    def test_public_mutation_corpus_is_rejected_as_reviewed(self) -> None:
        self.assertGreaterEqual(len(self.mutations), 10)
        with tempfile.TemporaryDirectory(prefix="eve-stage2-mutations-") as raw_temp:
            root = Path(raw_temp)
            for mutation in self.mutations:
                with self.subTest(mutation=mutation["id"]):
                    candidate = self.materialize(
                        mutation["route"],
                        mutation["base"],
                        mutation["operations"],
                        root,
                        label=mutation["id"],
                    )
                    report = EVALUATOR.evaluate_candidate(
                        mutation["route"], candidate
                    )
                    self.assertEqual(report["score"], 0.0, report)
                    self.assertIn(
                        mutation["expected_failure"], report["failure_codes"], report
                    )

    def test_case_seed_prefix_and_source_locks_are_frozen(self) -> None:
        source_hash = EVALUATOR.sha256(TASK_ROOT / "source-lock.json")
        for route in ("direct", "transport"):
            case = json.loads(
                (TASK_ROOT / route / "case.json").read_text(encoding="utf-8")
            )
            seed = TASK_ROOT / route / "seed" / "Candidate.lean"
            source = seed.read_text(encoding="utf-8")
            prefix = EVALUATOR._task_prefix(source, EVALUATOR.ROUTES[route]["marker"])
            self.assertIsNotNone(prefix)
            self.assertEqual(case["seed_candidate_sha256"], EVALUATOR.sha256(seed))
            self.assertEqual(
                case["protected_prefix_sha256"], EVALUATOR._sha256_text(prefix)
            )
            self.assertEqual(case["source_lock"]["sha256"], source_hash)

    def test_pair_evaluator_accepts_only_two_complete_matching_reports(self) -> None:
        gates = {name: True for name in EVALUATOR.GATE_NAMES}
        environment = {
            "lean_toolchain": EVALUATOR.EXPECTED_TOOLCHAIN,
            "mathlib_commit": EVALUATOR.EXPECTED_MATHLIB_COMMIT,
            "allowed_imports": EVALUATOR.ALLOWED_IMPORTS,
            "warning_allowlist": [],
        }
        with tempfile.TemporaryDirectory(prefix="eve-stage2-pair-") as raw_temp:
            root = Path(raw_temp)
            paths: dict[str, Path] = {}
            for route in ("direct", "transport"):
                paths[route] = root / f"{route}.json"
                paths[route].write_text(
                    json.dumps(
                        {
                            "task_id": PAIR.TASK_ID,
                            "route": route,
                            "status": "passed",
                            "score": 1.0,
                            "gates": gates,
                            "environment": environment,
                        }
                    ),
                    encoding="utf-8",
                )
            report = PAIR.evaluate_pair(paths["direct"], paths["transport"])
            self.assertEqual(report["status"], "passed", report)

            altered = json.loads(paths["transport"].read_text(encoding="utf-8"))
            altered["environment"] = {**environment, "mathlib_commit": "wrong"}
            paths["transport"].write_text(json.dumps(altered), encoding="utf-8")
            report = PAIR.evaluate_pair(paths["direct"], paths["transport"])
            self.assertEqual(report["score"], 0.0)
            self.assertIn("route-environments-differ", report["failure_codes"])


if __name__ == "__main__":
    unittest.main()
