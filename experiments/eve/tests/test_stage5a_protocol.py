"""Regression tests for the frozen, not-yet-executed Stage 5A protocol."""

from __future__ import annotations

import hashlib
import importlib.util
import io
import json
import os
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr
from pathlib import Path
from types import SimpleNamespace
from unittest import mock


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = SIDECAR_ROOT.parents[1]


def _load(name: str, relative: str):
    path = SIDECAR_ROOT / relative
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


RUNNER = _load("eve_stage5a_test_runner", "scripts/run_stage5a.py")
AUDITOR = _load("eve_stage5a_test_auditor", "scripts/audit_stage5a.py")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Stage5AProtocolTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.protocol = json.loads(
            (SIDECAR_ROOT / "stage5a_protocol.json").read_text(encoding="utf-8")
        )

    def test_stage4_history_and_frozen_inputs_are_unchanged(self) -> None:
        expected = {
            "stage4_protocol.json": "946c556ee5f2a13eafe57a5a5b7db55c3118febb715eaf34aaddd91caf74c037",
            "stage4_invalidated_attempts.json": "12593f39a625bfbeb362b264b746cbc95555b27537b7864e4831ddaf9dc3560d",
            "stage4_review/audit.json": "beae7fb17f06566b890b4a08635eafefc307276073afba4fdf46fcff4a86b9ad",
        }
        for relative, digest in expected.items():
            self.assertEqual(sha256(SIDECAR_ROOT / relative), digest)

        stage4 = json.loads(
            (SIDECAR_ROOT / "stage4_protocol.json").read_text(encoding="utf-8")
        )
        for relative, digest in stage4["frozen_artifacts"].items():
            self.assertEqual(sha256(REPO_ROOT / relative), digest, relative)

        local_audit = SIDECAR_ROOT / ".runtime" / "stage4-audit-machine.json"
        if local_audit.is_file():
            self.assertEqual(
                sha256(local_audit),
                "edc5332e822918bcf2635e01320f150825ad1d4e0c0b82a3acf20bc39b86142c",
            )

    def test_protocol_identity_hash_and_frozen_artifacts_verify(self) -> None:
        self.assertEqual(self.protocol["id"], RUNNER.PROTOCOL_ID)
        self.assertEqual(self.protocol["version"], RUNNER.PROTOCOL_VERSION)
        self.assertEqual(self.protocol["status"], "FROZEN_NOT_YET_EXECUTED")
        RUNNER.verify_protocol_assets()

    def test_prompt_is_byte_identical_across_conditions_for_each_route(self) -> None:
        recorded = self.protocol["solver_prompt_bundle_hashes"]
        for spec in RUNNER.SPECS.values():
            hashes = {
                condition: RUNNER.prompt_bundle_sha256(spec)
                for condition in RUNNER.CONDITIONS
            }
            self.assertEqual(len(set(hashes.values())), 1)
            self.assertEqual(next(iter(hashes.values())), recorded[spec.route])

            route_root = SIDECAR_ROOT / "overlay" / spec.overlay_key
            prompt_text = "\n".join(
                path.read_text(encoding="utf-8")
                for path in sorted((route_root / "prompt").rglob("*"))
                if path.is_file()
            )
            lowered = prompt_text.lower()
            for forbidden in (
                "static-no-specialized-guidance",
                "fixed-initial-guidance",
                "eve-evolved-guidance",
                "you are in the evolved",
            ):
                self.assertNotIn(forbidden, lowered)

    def test_local_checker_is_common_and_prompts_require_real_failure(self) -> None:
        direct = (
            SIDECAR_ROOT
            / "overlay/stage5a_entry_game_direct/immutable/STAGE5A_LEAN_CHECK.py"
        )
        transport = (
            SIDECAR_ROOT
            / "overlay/stage5a_entry_game_transport/immutable/STAGE5A_LEAN_CHECK.py"
        )
        self.assertEqual(direct.read_bytes(), transport.read_bytes())
        for spec in RUNNER.SPECS.values():
            entrypoint = (
                SIDECAR_ROOT / "overlay" / spec.overlay_key / "prompt" / "ENTRYPOINT.md"
            ).read_text(encoding="utf-8")
            self.assertIn("python3 STAGE5A_LEAN_CHECK.py", entrypoint)
            self.assertIn("actual\nrecorded Lean failure", entrypoint)
            self.assertIn("do not fabricate", entrypoint)
            self.assertIn("do not copy the complete proof", entrypoint)

    def test_local_checker_records_a_real_lean_failure(self) -> None:
        source = (
            SIDECAR_ROOT
            / "overlay/stage5a_entry_game_direct/immutable/STAGE5A_LEAN_CHECK.py"
        )
        with tempfile.TemporaryDirectory(prefix="stage5a-lean-check-") as raw_temp:
            workspace = Path(raw_temp)
            (workspace / "solver").mkdir()
            shutil.copy2(source, workspace / "STAGE5A_LEAN_CHECK.py")
            candidate = workspace / "solver" / "Candidate.lean"
            candidate.write_text(
                "def stage5aBroken : Nat := definitelyMissingName\n",
                encoding="utf-8",
            )
            completed = subprocess.run(
                [sys.executable, str(workspace / "STAGE5A_LEAN_CHECK.py")],
                cwd=workspace,
                env={**os.environ, "EVE_ECONCSLIB_ROOT": str(REPO_ROOT)},
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                check=False,
            )
            self.assertNotEqual(completed.returncode, 0)
            events_path = (
                workspace / ".scaling_evolve" / "stage5a-lean-checks.jsonl"
            )
            event = json.loads(events_path.read_text(encoding="utf-8").strip())
            self.assertTrue(event["failed"])
            self.assertNotEqual(event["stderr_bytes"] + event["stdout_bytes"], 0)
            self.assertEqual(event["candidate_sha256"], sha256(candidate))

    def test_state_retention_semantics_are_exact(self) -> None:
        expected = {"static": 0, "fixed": 0, "evolved": 1}
        for condition, production in expected.items():
            text = (
                SIDECAR_ROOT
                / "configs"
                / "eve"
                / "stage5a_condition"
                / f"{condition}.yaml"
            ).read_text(encoding="utf-8")
            self.assertIn(f"produce_optimizer_in_phase2: {production}", text)
        hashes = self.protocol["initial_guidance_tree_hashes"]
        self.assertEqual(
            hashes["entry-game-direct-fixed-and-evolved"],
            RUNNER.tree_sha256(
                SIDECAR_ROOT
                / "overlay/stage5a_entry_game_direct/initial_guidance"
            ),
        )
        self.assertEqual(
            hashes["entry-game-transport-fixed-and-evolved"],
            RUNNER.tree_sha256(
                SIDECAR_ROOT
                / "overlay/stage5a_entry_game_transport/initial_guidance"
            ),
        )

    def test_produced_and_selected_later_are_distinct_events(self) -> None:
        produced = {
            "event": "optimizer_candidate_produced",
            "candidate_id": "optimizer_new",
            "candidate_guidance_sha256": "a" * 64,
            "source_iteration": 1,
            "recorded_local_lean_failures": 1,
        }
        admitted = {
            "event": "optimizer_population_admission",
            "candidate_id": "optimizer_new",
            "candidate_guidance_sha256": "a" * 64,
            "source_iteration": 1,
            "admitted": True,
        }
        report = AUDITOR.classify_events(
            [produced, admitted], condition="evolved", iterations=3
        )
        self.assertEqual(report["produced_count"], 1)
        self.assertEqual(report["selected_later_count"], 0)
        self.assertEqual(report["status"], "PRODUCED_NOT_SELECTED_LATER")

        selected = {
            "event": "working_optimizer_sampled",
            "iteration": 2,
            "sampled": [
                {
                    "optimizer_id": "optimizer_new",
                    "guidance_sha256": "a" * 64,
                }
            ],
        }
        report = AUDITOR.classify_events(
            [produced, admitted, selected], condition="evolved", iterations=3
        )
        self.assertEqual(report["selected_later_count"], 1)
        self.assertEqual(report["failure_derived_selected_later_count"], 1)
        self.assertEqual(report["status"], "GUIDANCE_PRODUCED_AND_SELECTED_LATER")

        nonfailure_produced = {
            **produced,
            "candidate_id": "optimizer_nonfailure",
            "candidate_guidance_sha256": "d" * 64,
            "recorded_local_lean_failures": 0,
        }
        nonfailure_admitted = {
            **admitted,
            "candidate_id": "optimizer_nonfailure",
            "candidate_guidance_sha256": "d" * 64,
        }
        nonfailure_selected = {
            **selected,
            "sampled": [
                {
                    "optimizer_id": "optimizer_nonfailure",
                    "guidance_sha256": "d" * 64,
                }
            ],
        }
        report = AUDITOR.classify_events(
            [
                produced,
                admitted,
                nonfailure_produced,
                nonfailure_admitted,
                nonfailure_selected,
            ],
            condition="evolved",
            iterations=3,
        )
        self.assertEqual(report["selected_later_count"], 1)
        self.assertEqual(report["failure_derived_selected_later_count"], 0)
        self.assertEqual(report["status"], "PRODUCED_NOT_SELECTED_LATER")

    def test_no_subsequent_iteration_cannot_report_selected_later(self) -> None:
        events = [
            {
                "event": "optimizer_candidate_produced",
                "candidate_id": "optimizer_terminal",
                "candidate_guidance_sha256": "b" * 64,
                "source_iteration": 3,
                "recorded_local_lean_failures": 1,
            },
            {
                "event": "optimizer_population_admission",
                "candidate_id": "optimizer_terminal",
                "candidate_guidance_sha256": "b" * 64,
                "source_iteration": 3,
                "admitted": True,
            },
            {
                "event": "working_optimizer_sampled",
                "iteration": 3,
                "sampled": [
                    {
                        "optimizer_id": "optimizer_terminal",
                        "guidance_sha256": "b" * 64,
                    }
                ],
            },
        ]
        report = AUDITOR.classify_events(
            events, condition="evolved", iterations=3
        )
        self.assertEqual(report["selected_later_count"], 0)
        self.assertEqual(report["status"], "PRODUCED_WITHOUT_LATER_OPPORTUNITY")

    def test_controls_cannot_retain_changed_guidance(self) -> None:
        produced = {
            "event": "optimizer_candidate_produced",
            "candidate_id": "forbidden",
            "candidate_guidance_sha256": "c" * 64,
            "source_iteration": 1,
            "recorded_local_lean_failures": 1,
        }
        for condition in ("static", "fixed"):
            report = AUDITOR.classify_events(
                [produced], condition=condition, iterations=3
            )
            self.assertEqual(report["status"], "INVALID_CONTROL_GUIDANCE_RETENTION")

    def test_post_run_audit_joins_telemetry_to_read_only_lineage_artifact(self) -> None:
        with tempfile.TemporaryDirectory(prefix="stage5a-audit-fixture-") as raw_temp:
            runs_root = Path(raw_temp) / "stage5a-runs"
            run_root = runs_root / "fresh-run"
            run_root.mkdir(parents=True)
            protocol_hash = (SIDECAR_ROOT / "stage5a_protocol.sha256").read_text(
                encoding="utf-8"
            ).split()[0]
            launch = {
                "protocol_id": RUNNER.PROTOCOL_ID,
                "protocol_sha256": protocol_hash,
                "protocol_status_at_launch": "FROZEN_NOT_YET_EXECUTED",
                "run_root": str(run_root.resolve()),
                "experiment": "entry-game-direct",
                "route": "direct",
                "condition": "evolved",
                "experiment_seed": 1729,
                "iterations": 3,
                "resume": False,
                "import": False,
                "retry": False,
                "attempt_limit": 1,
                "provider_model_seed_controlled": False,
                "solver_prompt_bundle_sha256": self.protocol[
                    "solver_prompt_bundle_hashes"
                ]["direct"],
                "initial_guidance_tree_sha256": self.protocol[
                    "initial_guidance_tree_hashes"
                ]["entry-game-direct-fixed-and-evolved"],
                "status": "completed",
                "exit_code": 0,
            }
            (run_root / "stage5a-launch.json").write_text(
                json.dumps(launch), encoding="utf-8"
            )
            guidance_files = {"docs/learned.md": "Use the compiler error shape.\n"}
            guidance_hash = AUDITOR.tree_sha256(guidance_files)
            (run_root / "eve-stage5a-sampler-seed.json").write_text(
                json.dumps(
                    {
                        "provider_model_seed_controlled": False,
                        "experiment_seed": 1729,
                    }
                ),
                encoding="utf-8",
            )
            events = [
                {
                    "event": "factory_seeded",
                    "provider_model_seed_controlled": False,
                },
                {
                    "event": "working_optimizer_sampled",
                    "iteration": 1,
                    "sampled": [
                        {"optimizer_id": "optimizer_seed", "guidance_sha256": "0" * 64}
                    ],
                },
                {
                    "event": "solver_guidance_loaded",
                    "iteration": 1,
                    "optimizer_id": "optimizer_seed",
                    "guidance_sha256": "0" * 64,
                    "workspace_guidance_sha256": "0" * 64,
                    "matches_sampled_optimizer": True,
                },
                {
                    "event": "solver_rollout_completed",
                    "iteration": 1,
                    "workspace_id": "workspace_1",
                    "initial_guidance_sha256": "0" * 64,
                    "final_guidance_sha256": guidance_hash,
                    "guidance_tree_changed": True,
                    "recorded_local_lean_failures": 1,
                    "lean_checker_unchanged": True,
                },
                {
                    "event": "optimizer_candidate_produced",
                    "candidate_id": "optimizer_new",
                    "candidate_guidance_sha256": guidance_hash,
                    "source_iteration": 1,
                    "workspace_id": "workspace_1",
                    "parent_guidance_sha256": "0" * 64,
                    "recorded_local_lean_failures": 1,
                },
                {
                    "event": "optimizer_population_admission",
                    "candidate_id": "optimizer_new",
                    "candidate_guidance_sha256": guidance_hash,
                    "source_iteration": 1,
                    "admitted": True,
                },
                {
                    "event": "working_optimizer_sampled",
                    "iteration": 2,
                    "sampled": [
                        {"optimizer_id": "optimizer_new", "guidance_sha256": guidance_hash}
                    ],
                },
                {
                    "event": "solver_guidance_loaded",
                    "iteration": 2,
                    "optimizer_id": "optimizer_new",
                    "guidance_sha256": guidance_hash,
                    "workspace_guidance_sha256": guidance_hash,
                    "matches_sampled_optimizer": True,
                },
                {
                    "event": "solver_rollout_completed",
                    "iteration": 2,
                    "workspace_id": "workspace_2",
                    "initial_guidance_sha256": guidance_hash,
                    "final_guidance_sha256": guidance_hash,
                    "guidance_tree_changed": False,
                    "recorded_local_lean_failures": 0,
                    "lean_checker_unchanged": True,
                },
                {
                    "event": "working_optimizer_sampled",
                    "iteration": 3,
                    "sampled": [
                        {"optimizer_id": "optimizer_seed", "guidance_sha256": "0" * 64}
                    ],
                },
                {
                    "event": "solver_guidance_loaded",
                    "iteration": 3,
                    "optimizer_id": "optimizer_seed",
                    "guidance_sha256": "0" * 64,
                    "workspace_guidance_sha256": "0" * 64,
                    "matches_sampled_optimizer": True,
                },
                {
                    "event": "solver_rollout_completed",
                    "iteration": 3,
                    "workspace_id": "workspace_3",
                    "initial_guidance_sha256": "0" * 64,
                    "final_guidance_sha256": "0" * 64,
                    "guidance_tree_changed": False,
                    "recorded_local_lean_failures": 0,
                    "lean_checker_unchanged": True,
                },
            ]
            (run_root / "stage5a-guidance-lineage.jsonl").write_text(
                "".join(json.dumps(event) + "\n" for event in events),
                encoding="utf-8",
            )
            relative = Path("optimizer-run/state/optimizer_new.json")
            artifact = run_root / "artifacts" / relative
            artifact.parent.mkdir(parents=True)
            artifact.write_text(json.dumps(guidance_files), encoding="utf-8")
            connection = sqlite3.connect(run_root / "optimizer_lineage.db")
            connection.execute(
                "CREATE TABLE eve_population_entries ("
                "run_id TEXT, app_kind TEXT, entry_id TEXT, files_ref_json TEXT)"
            )
            connection.execute(
                "INSERT INTO eve_population_entries VALUES (?, ?, ?, ?)",
                (
                    "fresh_optimizer",
                    "eve.optimizer",
                    "optimizer_new",
                    json.dumps(
                        {
                            "relpath": relative.as_posix(),
                            "sha256": sha256(artifact),
                        }
                    ),
                ),
            )
            connection.commit()
            connection.close()
            with mock.patch.object(AUDITOR, "RUNS_ROOT", runs_root.resolve()):
                report = AUDITOR.audit_run(run_root)
            self.assertTrue(report["lineage_database_verified"])
            self.assertEqual(report["status"], "GUIDANCE_PRODUCED_AND_SELECTED_LATER")

    def test_transport_has_all_ten_frozen_checkpoints(self) -> None:
        path = (
            SIDECAR_ROOT
            / "overlay/stage5a_entry_game_transport/immutable/TRANSPORT_CHECKPOINTS.md"
        )
        text = path.read_text(encoding="utf-8")
        numbered = [line for line in text.splitlines() if line[:1].isdigit()]
        self.assertEqual(len(numbered), 10)
        for phrase in (
            "exact final concrete theorem signatures",
            "action encoders and the profile encoder",
            "payoff preservation",
            "strict assumptions",
            "Nash and subgame-perfect-equilibrium preservation",
            "complete `RefinementCertificate`",
            "consume the certificate's preservation projections",
            "fixed general `AbstractTwoStage` theorems",
            "equality reflection",
            "concrete profile type",
        ):
            self.assertIn(phrase, text)

    def test_fresh_root_and_no_retry_resume_or_import(self) -> None:
        compute = self.protocol["shared_compute"]
        self.assertEqual(compute["fresh_run_root_parent"], "experiments/eve/.runtime/stage5a-runs")
        self.assertFalse(compute["retry"])
        self.assertFalse(compute["resume"])
        self.assertFalse(compute["import"])
        self.assertEqual(compute["attempts_per_matrix_cell"], 1)
        root = RUNNER._new_run_root()
        self.assertEqual(root.parent, RUNNER.RUNS_ROOT.resolve())
        self.assertFalse(root.exists())
        source = (SIDECAR_ROOT / "scripts/run_stage5a.py").read_text(encoding="utf-8")
        self.assertNotIn(".runtime/runs/", source)

    def test_check_and_dry_run_dispatch_never_execute(self) -> None:
        identity = SimpleNamespace(root=Path("/tmp/eve"), commit="0" * 40)
        common = [
            "--eve-checkout", "/tmp/eve",
            "--experiment", "entry-game-direct",
            "--protocol-id", RUNNER.PROTOCOL_ID,
            "--condition", "static",
            "--experiment-seed", "1729",
        ]
        with (
            mock.patch.object(RUNNER.BASE, "verify_checkout", return_value=identity),
            mock.patch.object(RUNNER, "check", return_value=0) as checked,
            mock.patch.object(RUNNER, "dry_run", return_value=0) as dried,
            mock.patch.object(RUNNER, "execute", side_effect=AssertionError("model path called")),
        ):
            self.assertEqual(RUNNER.main([*common, "--check"]), 0)
            self.assertEqual(RUNNER.main([*common, "--dry-run"]), 0)
            self.assertEqual(checked.call_count, 1)
            self.assertEqual(dried.call_count, 1)

    def test_invalid_task_condition_seed_or_protocol_hard_fails(self) -> None:
        with self.assertRaises(RUNNER.CheckError):
            RUNNER.validate_selection(
                protocol_id="wrong", condition="static", experiment_seed=1729
            )
        with self.assertRaises(RUNNER.CheckError):
            RUNNER.validate_selection(
                protocol_id=RUNNER.PROTOCOL_ID,
                condition="invalid",
                experiment_seed=1729,
            )
        with self.assertRaises(RUNNER.CheckError):
            RUNNER.validate_selection(
                protocol_id=RUNNER.PROTOCOL_ID,
                condition="static",
                experiment_seed=999,
            )
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            RUNNER._parser().parse_args(
                [
                    "--eve-checkout", "/tmp/eve",
                    "--experiment", "not-a-task",
                    "--protocol-id", RUNNER.PROTOCOL_ID,
                    "--condition", "static",
                    "--experiment-seed", "1729",
                    "--dry-run",
                ]
            )

    def test_protocol_declares_not_executed_claim_boundary(self) -> None:
        boundary = self.protocol["claim_boundary"]
        self.assertIn("no new guidance has been produced or selected", boundary)
        self.assertIn("Luna has not run under Stage 5A", boundary)
        self.assertIn("Sol replication has not begun", boundary)
        self.assertEqual(self.protocol["review"]["kind"], "codex-ai-review")
        self.assertFalse(self.protocol["review"]["independent_human_review"])


if __name__ == "__main__":
    unittest.main()
