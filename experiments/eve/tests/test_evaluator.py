"""Unit and integration tests for the deterministic public smoke evaluator."""

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


SIDECAR_ROOT = Path(__file__).resolve().parents[1]


def _load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


EVALUATOR = _load_module(
    "eve_smoke_evaluator", SIDECAR_ROOT / "scripts" / "evaluate_smoke.py"
)


class EvaluatorTests(unittest.TestCase):
    def evaluate_fixture(self, name: str, *, extra_file: bool = False):
        with tempfile.TemporaryDirectory(prefix="econcslib-eve-test-") as raw_temp:
            candidate = Path(raw_temp) / "candidate"
            shutil.copytree(SIDECAR_ROOT / "smoke" / "seed", candidate)
            shutil.copy2(
                SIDECAR_ROOT / "smoke" / "expected" / name,
                candidate / "Candidate.lean",
            )
            if extra_file:
                (candidate / "Forbidden.txt").write_text(
                    "forbidden\n", encoding="utf-8"
                )
            return EVALUATOR.evaluate_candidate(candidate)

    def test_correct_repair_passes(self) -> None:
        report = self.evaluate_fixture("Accepted.lean")
        self.assertEqual(report["status"], "passed")
        self.assertEqual(report["score"], 1.0)
        self.assertTrue(all(report["gates"].values()))

    def test_unfixed_issue_fails(self) -> None:
        report = self.evaluate_fixture("Unfixed.lean")
        self.assertEqual(report["score"], 0.0)
        self.assertIn("target-issue-unresolved", report["failure_codes"])
        self.assertIn("unexpected-warning", report["failure_codes"])

    def test_compile_failure_fails(self) -> None:
        report = self.evaluate_fixture("CompileFailure.lean")
        self.assertEqual(report["score"], 0.0)
        self.assertIn("compile-failed", report["failure_codes"])

    def test_placeholder_axiom_and_constant_bypasses_fail(self) -> None:
        for fixture in ("Placeholder.lean", "Axiom.lean", "Constant.lean"):
            with self.subTest(fixture=fixture):
                report = self.evaluate_fixture(fixture)
                self.assertEqual(report["score"], 0.0)
                self.assertIn("forbidden-construct", report["failure_codes"])

    def test_boundary_violation_is_worst_score(self) -> None:
        report = self.evaluate_fixture("Accepted.lean", extra_file=True)
        self.assertEqual(report["score"], 0.0)
        self.assertTrue(
            any(
                code.startswith("forbidden-created:")
                for code in report["failure_codes"]
            )
        )
        self.assertFalse(report["gates"]["compile"])

    def test_score_yaml_has_exact_eve_shape(self) -> None:
        with tempfile.TemporaryDirectory(prefix="econcslib-eve-score-") as raw_temp:
            path = Path(raw_temp) / "score.yaml"
            EVALUATOR.write_score(
                path,
                {"score": 1.0, "summary": "all deterministic smoke gates passed"},
            )
            self.assertEqual(
                path.read_text(encoding="utf-8"),
                'score: 1.0\nsummary: "all deterministic smoke gates passed"\n',
            )

    def test_eve_shell_step_writes_score_in_eval_log_root(self) -> None:
        with tempfile.TemporaryDirectory(prefix="econcslib-eve-shell-") as raw_temp:
            workspace = Path(raw_temp) / "workspace"
            solver = workspace / "solver"
            log_root = workspace / "logs" / "evaluate"
            shutil.copytree(SIDECAR_ROOT / "smoke" / "seed", solver)
            shutil.copy2(
                SIDECAR_ROOT / "smoke" / "expected" / "Accepted.lean",
                solver / "Candidate.lean",
            )
            completed = subprocess.run(
                ["bash", str(SIDECAR_ROOT / "scripts" / "evaluation.sh")],
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
                'score: 1.0\nsummary: "all deterministic smoke gates passed"\n',
            )
            report = json.loads(
                (log_root / "evaluation.json").read_text(encoding="utf-8")
            )
            self.assertEqual(report["status"], "passed")

    def test_repeated_evaluation_is_identical(self) -> None:
        first = self.evaluate_fixture("Accepted.lean")
        second = self.evaluate_fixture("Accepted.lean")
        self.assertEqual(first, second)

    def test_seed_hash_is_frozen(self) -> None:
        case = json.loads(
            (SIDECAR_ROOT / "smoke" / "case.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            case["seed_candidate_sha256"],
            EVALUATOR._sha256(SIDECAR_ROOT / "smoke" / "seed" / "Candidate.lean"),
        )


if __name__ == "__main__":
    unittest.main()
