"""Positive and negative tests for the deterministic Stage 1a EFG evaluator."""

from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
TASK_ROOT = SIDECAR_ROOT / "efg_reachability_micro"


def _load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


EVALUATOR = _load_module(
    "eve_efg_micro_evaluator",
    SIDECAR_ROOT / "scripts" / "evaluate_efg_reachability_micro.py",
)


class EFGMicroEvaluatorTests(unittest.TestCase):
    def evaluate_fixture(self, name: str, *, extra_file: bool = False):
        with tempfile.TemporaryDirectory(prefix="econcslib-eve-efg-test-") as raw_temp:
            candidate = Path(raw_temp) / "candidate"
            shutil.copytree(TASK_ROOT / "seed", candidate)
            if name == "Unfixed.lean":
                fixture = TASK_ROOT / "seed" / "Candidate.lean"
            else:
                fixture = TASK_ROOT / "expected" / name
            shutil.copy2(fixture, candidate / "Candidate.lean")
            if extra_file:
                (candidate / "Forbidden.txt").write_text(
                    "forbidden\n", encoding="utf-8"
                )
            return EVALUATOR.evaluate_candidate(candidate)

    def test_accepted_fixture_passes_every_gate(self) -> None:
        report = self.evaluate_fixture("Accepted.lean")
        self.assertEqual(report["status"], "passed")
        self.assertEqual(report["score"], 1.0)
        self.assertTrue(all(report["gates"].values()))
        self.assertEqual(report["failure_codes"], [])

    def test_unfixed_seed_fails_exact_declaration_contract(self) -> None:
        report = self.evaluate_fixture("Unfixed.lean")
        self.assertEqual(report["score"], 0.0)
        self.assertIn(
            "target-declaration-missing-or-wrong-type", report["failure_codes"]
        )

    def test_compile_failure_fails(self) -> None:
        report = self.evaluate_fixture("CompileFailure.lean")
        self.assertEqual(report["score"], 0.0)
        self.assertIn("compile-failed", report["failure_codes"])

    def test_placeholder_axiom_and_constant_spoofs_fail(self) -> None:
        for fixture in ("Placeholder.lean", "Axiom.lean", "Constant.lean"):
            with self.subTest(fixture=fixture):
                report = self.evaluate_fixture(fixture)
                self.assertEqual(report["score"], 0.0)
                self.assertIn("forbidden-construct", report["failure_codes"])
                self.assertFalse(report["gates"]["compile"])

    def test_boundary_violation_is_worst_score_before_lean(self) -> None:
        report = self.evaluate_fixture("Accepted.lean", extra_file=True)
        self.assertEqual(report["score"], 0.0)
        self.assertTrue(
            any(
                code.startswith("forbidden-created:")
                for code in report["failure_codes"]
            )
        )
        self.assertFalse(report["gates"]["compile"])

    def test_broad_and_additional_imports_fail_before_lean(self) -> None:
        for fixture in ("BroadImport.lean", "AdditionalImport.lean"):
            with self.subTest(fixture=fixture):
                report = self.evaluate_fixture(fixture)
                self.assertEqual(report["score"], 0.0)
                self.assertIn("forbidden-import", report["failure_codes"])
                self.assertFalse(report["gates"]["compile"])

    def test_wrong_bridge_type_fails_exact_contract(self) -> None:
        report = self.evaluate_fixture("WrongTheoremType.lean")
        self.assertEqual(report["score"], 0.0)
        self.assertTrue(report["gates"]["compile"])
        self.assertIn(
            "target-declaration-missing-or-wrong-type", report["failure_codes"]
        )

    def test_missing_diamond_regression_fails(self) -> None:
        report = self.evaluate_fixture("MissingDiamond.lean")
        self.assertEqual(report["score"], 0.0)
        self.assertTrue(report["gates"]["target_declaration"])
        self.assertIn(
            "diamond-regression-missing-or-invalid", report["failure_codes"]
        )

    def test_protected_asset_mismatch_fails_before_lean(self) -> None:
        with tempfile.TemporaryDirectory(prefix="econcslib-eve-protected-") as raw_temp:
            candidate = Path(raw_temp) / "candidate"
            shutil.copytree(TASK_ROOT / "seed", candidate)
            shutil.copy2(
                TASK_ROOT / "expected" / "Accepted.lean",
                candidate / "Candidate.lean",
            )
            with mock.patch.object(
                EVALUATOR,
                "_expected_protected_failures",
                return_value=["protected-asset-hash-mismatch:fixture"],
            ):
                with mock.patch.object(
                    EVALUATOR,
                    "_compile_source",
                    side_effect=AssertionError("Lean must not run"),
                ):
                    report = EVALUATOR.evaluate_candidate(candidate)
        self.assertEqual(report["score"], 0.0)
        self.assertIn(
            "protected-asset-hash-mismatch:fixture", report["failure_codes"]
        )
        self.assertFalse(report["gates"]["compile"])

    def test_score_yaml_has_exact_eve_shape(self) -> None:
        with tempfile.TemporaryDirectory(prefix="econcslib-eve-efg-score-") as raw_temp:
            path = Path(raw_temp) / "score.yaml"
            EVALUATOR.write_score(
                path,
                {
                    "score": 1.0,
                    "summary": "all deterministic EFG micro-pilot gates passed",
                },
            )
            self.assertEqual(
                path.read_text(encoding="utf-8"),
                'score: 1.0\nsummary: "all deterministic EFG micro-pilot gates passed"\n',
            )

    def test_shell_step_writes_only_public_score_schema(self) -> None:
        with tempfile.TemporaryDirectory(prefix="econcslib-eve-efg-shell-") as raw_temp:
            workspace = Path(raw_temp) / "workspace"
            solver = workspace / "solver"
            log_root = workspace / "logs" / "evaluate"
            shutil.copytree(TASK_ROOT / "seed", solver)
            shutil.copy2(
                TASK_ROOT / "expected" / "Accepted.lean",
                solver / "Candidate.lean",
            )
            completed = subprocess.run(
                [
                    "bash",
                    str(
                        SIDECAR_ROOT
                        / "scripts"
                        / "evaluation_efg_reachability_micro.sh"
                    ),
                ],
                cwd=workspace,
                env={
                    **os.environ,
                    "EVE_ECONCSLIB_ROOT": str(SIDECAR_ROOT.parents[1]),
                    "EVE_SOLVER_ROOT": str(solver),
                    "EVE_EVAL_LOG_ROOT": str(log_root),
                },
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(completed.returncode, 0, completed.stdout)
            self.assertEqual(
                (log_root / "score.yaml").read_text(encoding="utf-8"),
                'score: 1.0\nsummary: "all deterministic EFG micro-pilot gates passed"\n',
            )
            report = json.loads(
                (log_root / "evaluation.json").read_text(encoding="utf-8")
            )
            self.assertEqual(report["status"], "passed")

    def test_seed_and_prefix_hashes_are_frozen(self) -> None:
        case = json.loads((TASK_ROOT / "case.json").read_text(encoding="utf-8"))
        source = (TASK_ROOT / "seed" / "Candidate.lean").read_text(
            encoding="utf-8"
        )
        prefix = EVALUATOR._task_prefix(source)
        self.assertIsNotNone(prefix)
        self.assertEqual(
            case["seed_candidate_sha256"],
            EVALUATOR.sha256(TASK_ROOT / "seed" / "Candidate.lean"),
        )
        self.assertEqual(
            case["protected_prefix_sha256"], EVALUATOR._sha256_text(prefix)
        )

    def test_solver_prompt_metadata_and_hash_are_frozen(self) -> None:
        case = json.loads((TASK_ROOT / "case.json").read_text(encoding="utf-8"))
        prompt = case["solver_prompt"]
        prompt_path = SIDECAR_ROOT.parents[1] / prompt["entrypoint"]
        actual_hash = EVALUATOR.sha256(prompt_path)

        self.assertEqual(prompt["id"], "EVE-EFG-SOLVER-PROMPT-001")
        self.assertEqual(prompt["version"], "1.0.0")
        self.assertTrue(prompt["model_neutral"])
        self.assertEqual(prompt["status"], "EXECUTED_SCORE_ZERO_THEN_SCORE_ONE")
        self.assertEqual(
            prompt["latest_execution_prompt_id"],
            "EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-002",
        )
        self.assertEqual(
            [item["score"] for item in prompt["execution_history"]], [0.0, 1.0]
        )
        self.assertEqual(prompt["entrypoint_sha256"], actual_hash)
        self.assertEqual(case["protected_assets"][prompt["entrypoint"]], actual_hash)


if __name__ == "__main__":
    unittest.main()
