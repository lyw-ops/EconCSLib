"""Regressions for the frozen, zero-model-call Stage 5B Sol REP-003 protocol."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import platform
import shutil
import sqlite3
import sys
import tempfile
import unittest
from contextlib import ExitStack
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


RUNNER = _load("eve_stage5b_sol_rep003_test_runner", "scripts/run_stage5b_sol_rep003.py")
AUDITOR = _load("eve_stage5b_sol_rep003_test_auditor", "scripts/audit_stage5b_sol_rep003.py")
TERMINAL = _load(
    "eve_stage5b_sol_rep003_test_terminal",
    "scripts/stage5b_sol_rep003_terminal.py",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_check_event(
    *,
    sequence: int = 1,
    previous: str | None = None,
    checker_hash: str = "f" * 64,
    candidate_hash: str = "c" * 64,
    guidance_hash: str = "0" * 64,
    failed: bool = True,
) -> dict[str, object]:
    event: dict[str, object] = {
        "schema_version": "2.0.0",
        "sequence": sequence,
        "previous_event_sha256": previous,
        "observed_at": "2026-08-21T00:00:00+00:00",
        "python_invocation": "/usr/bin/python3",
        "python_executable": "/Library/Developer/CommandLineTools/usr/bin/python3",
        "python_version": "3.9.6",
        "command": ["lake", "env", "lean", "solver/Candidate.lean"],
        "checker_sha256": checker_hash,
        "candidate_sha256": candidate_hash,
        "guidance_sha256": guidance_hash,
        "exit_code": 1 if failed else 0,
        "failed": failed,
        "stdout_sha256": "d" * 64,
        "stderr_sha256": "e" * 64,
        "stdout_bytes": 0,
        "stderr_bytes": 1 if failed else 0,
    }
    event["event_sha256"] = AUDITOR.event_sha256(event)
    return event


def hook_guard_evidence() -> dict[str, object]:
    return {
        "schema_version": "1.0.0",
        "phase": "pre-reservation-pre-formal-root-pre-model",
        "eve_checkout": "/tmp/pinned-eve",
        "hooks_path": "/tmp/pinned-eve/.codex/hooks.json",
        "operation": "write_repo_codex_hooks/write_codex_hooks_file/Path.write_text",
        "upstream_runner_sha256": AUDITOR.EXPECTED_UPSTREAM_RUNNER_SHA256,
        "upstream_hook_writer_sha256": AUDITOR.EXPECTED_UPSTREAM_HOOK_WRITER_SHA256,
        "content_before_sha256": "1" * 64,
        "content_after_sha256": "1" * 64,
        "idempotent_double_write_verified": True,
        "project_trusted": True,
        "missing_hook_trust_events": [],
        "model_calls": 0,
        "sol_quota_consumed": 0,
        "formal_run_root_written": False,
        "formal_attempt_ledger_written": False,
        "formal_state_projection_unchanged": True,
        "historical_state_projection_unchanged": True,
        "formal_state_before_sha256": "2" * 64,
        "formal_state_after_sha256": "2" * 64,
        "historical_state_before_sha256": "3" * 64,
        "historical_state_after_sha256": "3" * 64,
        "quiescence": {
            name: {
                "label": name,
                "stable_samples_required": 3,
                "samples_observed": 3,
                "poll_seconds": 0.05,
                "timeout_seconds": 30.0,
            }
            for name in (
                "formal_before",
                "formal_after",
                "historical_before",
                "historical_after",
            )
        },
    }


class Stage5BSolRep003ProtocolTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.protocol = json.loads(
            (SIDECAR_ROOT / "stage5b_sol_rep003_protocol.json").read_text(
                encoding="utf-8"
            )
        )

    def test_protocol_identity_hash_and_frozen_assets_verify(self) -> None:
        self.assertEqual(self.protocol["id"], RUNNER.PROTOCOL_ID)
        self.assertEqual(self.protocol["version"], "1.0.0")
        self.assertEqual(self.protocol["status"], "FROZEN_NOT_YET_EXECUTED")
        RUNNER.verify_protocol_assets()

    def test_dev001_dev002_and_dev003_evidence_remain_historical(self) -> None:
        old = json.loads(
            (SIDECAR_ROOT / "stage5a_protocol.json").read_text(encoding="utf-8")
        )
        executed = json.loads(
            (SIDECAR_ROOT / "stage5a_review/dev002-execution-audit.json").read_text(
                encoding="utf-8"
            )
        )
        invalidated = json.loads(
            (SIDECAR_ROOT / "stage5a_invalidated_protocols.json").read_text(
                encoding="utf-8"
            )
        )["records"][0]
        self.assertEqual(old["status"], "FROZEN_NOT_YET_EXECUTED")
        self.assertEqual(executed["status"], "EXECUTED_PROTOCOL_DEFECT_DETECTED")
        self.assertEqual(invalidated["classification"], "invalidated-before-execution")
        self.assertEqual(
            self.protocol["historical_stage5a_protocols"]["dev002_protocol_id"],
            old["id"],
        )
        dev003 = json.loads(
            (SIDECAR_ROOT / "stage5a_dev003_protocol.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            self.protocol["replicates_stage5a_dev003"]["protocol_id"], dev003["id"]
        )

    def test_committed_lean_closure_ignores_mixed_worktree(self) -> None:
        environment = RUNNER.load_lean_environment(self.protocol)
        RUNNER.verify_manifest_against_source_commit(environment)
        self.assertEqual(environment["source_commit"], RUNNER.SOURCE_COMMIT)
        self.assertEqual(len(environment["local_import_closure"]), 109)
        self.assertIn(
            "separate tracked-clean checkout",
            environment["source_policy"],
        )

    def test_checkers_are_identical_python39_compatible_entrypoints(self) -> None:
        paths = [
            SIDECAR_ROOT / "overlay" / spec.overlay_key / "immutable" / "STAGE5A_LEAN_CHECK.py"
            for spec in RUNNER.SPECS.values()
        ]
        self.assertEqual(paths[0].read_bytes(), paths[1].read_bytes())
        source = paths[0].read_text(encoding="utf-8")
        self.assertIn("dt.timezone.utc", source)
        self.assertNotIn("dt.UTC", source)
        self.assertIn('EXPECTED_PYTHON_VERSION = "3.9.6"', source)
        completed = __import__("subprocess").run(
            ["/usr/bin/python3", "-c", f"compile(open({str(paths[0])!r}).read(), 'checker', 'exec')"],
            stdout=__import__("subprocess").PIPE,
            stderr=__import__("subprocess").PIPE,
            check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr.decode())

    def test_scientific_inputs_match_rep002_and_dev003_byte_for_byte(self) -> None:
        dev003 = json.loads(
            (SIDECAR_ROOT / "stage5a_dev003_protocol.json").read_text(encoding="utf-8")
        )
        rep002 = json.loads(
            (SIDECAR_ROOT / "stage5b_sol_rep002_protocol.json").read_text(
                encoding="utf-8"
            )
        )
        for key in (
            "tasks",
            "conditions",
            "experiment_seeds",
            "run_matrix",
            "run_matrix_size",
            "model_sessions_per_run",
            "maximum_model_sessions",
            "solver_prompt_bundle_hashes",
            "initial_guidance_tree_hashes",
            "condition_state_semantics",
            "condition_neutral_prompt_contract",
            "edit_surfaces",
        ):
            self.assertEqual(self.protocol[key], dev003[key], key)
            self.assertEqual(self.protocol[key], rep002[key], key)
        for key in (
            "iterations",
            "minimum_iterations_for_produced_then_selected",
            "workers_per_iteration",
            "solver_examples",
            "optimizer_examples",
            "produced_optimizers_per_iteration",
            "boundary_repairs",
            "resume",
            "import",
            "retry",
            "attempts_per_matrix_cell",
        ):
            self.assertEqual(
                self.protocol["shared_compute"][key], dev003["shared_compute"][key], key
            )
            self.assertEqual(
                self.protocol["shared_compute"][key], rep002["shared_compute"][key], key
            )
        for key in ("reasoning_effort", "rollout_max_turns", "web_search", "timeout_seconds"):
            self.assertEqual(self.protocol["model"][key], dev003["model"][key], key)
        for route in ("direct", "transport"):
            new_root = SIDECAR_ROOT / "overlay" / f"stage5b_sol_rep003_entry_game_{route}"
            old_root = SIDECAR_ROOT / "overlay" / f"stage5b_sol_rep002_entry_game_{route}"
            new_files = sorted(path.relative_to(new_root) for path in new_root.rglob("*") if path.is_file())
            old_files = sorted(path.relative_to(old_root) for path in old_root.rglob("*") if path.is_file())
            self.assertEqual(new_files, old_files)
            for relative in new_files:
                self.assertEqual((new_root / relative).read_bytes(), (old_root / relative).read_bytes(), relative)
        for stem in (
            "run_stage5b_sol_rep003_eve.py",
            "stage5b_sol_rep003_terminal.py",
        ):
            new = (SIDECAR_ROOT / "scripts" / stem).read_text(encoding="utf-8")
            old = (
                SIDECAR_ROOT
                / "scripts"
                / stem.replace("rep003", "rep002")
            ).read_text(encoding="utf-8")
            self.assertEqual(
                new.replace("rep003", "rep002").replace("REP-003", "REP-002").replace("REP003", "REP002"),
                old,
                stem,
            )

    def test_hook_guard_uses_pinned_real_write_and_trust_helpers(self) -> None:
        source = (SIDECAR_ROOT / "scripts/run_stage5b_sol_rep003.py").read_text(
            encoding="utf-8"
        )
        guard = source[
            source.index("def pre_reservation_hook_guard(") : source.index(
                "def safe_preflight("
            )
        ]
        self.assertGreaterEqual(guard.count("write_repo_codex_hooks(root)"), 2)
        self.assertIn("ensure_codex_hooks_trusted(root)", guard)
        self.assertIn('root / ".codex" / "hooks.json"', guard)
        self.assertIn("Path.write_text", guard)
        self.assertNotIn("os.access", guard)

    def test_hook_write_failure_touches_no_ledger_root_or_model(self) -> None:
        with tempfile.TemporaryDirectory(prefix="sol-rep003-hook-fail-") as raw:
            temp = Path(raw)
            runs = temp / "formal-runs"
            ledger = temp / "formal-ledger.sqlite3"
            identity = SimpleNamespace(root=temp / "eve", commit="5" * 40)
            reserve = mock.Mock()
            new_root = mock.Mock()
            dispatch = mock.Mock()
            with mock.patch.object(
                RUNNER,
                "pre_reservation_hook_guard",
                side_effect=RUNNER.CheckError("simulated Path.write_text denial"),
            ), mock.patch.object(RUNNER, "reserve_attempt", reserve), mock.patch.object(
                RUNNER, "_new_run_root", new_root
            ), mock.patch.object(RUNNER.subprocess, "run", dispatch), mock.patch.object(
                RUNNER, "RUNS_ROOT", runs
            ), mock.patch.object(RUNNER, "ATTEMPT_LEDGER_PATH", ledger):
                with self.assertRaises(RUNNER.CheckError):
                    RUNNER.execute(
                        identity,
                        RUNNER.SPECS["entry-game-direct"],
                        condition="static",
                        seed=1729,
                        lean_checkout=temp / "lean",
                        acknowledge_model_quota=True,
                    )
            reserve.assert_not_called()
            new_root.assert_not_called()
            dispatch.assert_not_called()
            self.assertFalse(runs.exists())
            self.assertFalse(ledger.exists())

    def test_successful_hook_guard_reaches_reservation_seam_only_after_all_gates(self) -> None:
        class ReservationReached(RuntimeError):
            pass

        order: list[str] = []
        identity = SimpleNamespace(root=Path("/tmp/pinned-eve"), commit="5" * 40)
        protocol = {"status": "FROZEN_NOT_YET_EXECUTED"}
        with tempfile.TemporaryDirectory(prefix="sol-rep003-reservation-") as raw:
            temp = Path(raw)
            with ExitStack() as stack:
                stack.enter_context(
                    mock.patch.object(
                        RUNNER,
                        "pre_reservation_hook_guard",
                        side_effect=lambda _identity: order.append("hook") or {"ok": True},
                    )
                )
                stack.enter_context(
                    mock.patch.object(RUNNER, "verify_protocol_assets", return_value=protocol)
                )
                stack.enter_context(mock.patch.object(RUNNER, "load_lean_environment", return_value={}))
                stack.enter_context(
                    mock.patch.object(RUNNER, "verify_clean_lean_checkout", return_value=temp)
                )
                stack.enter_context(mock.patch.object(RUNNER, "verify_upstream_semantics"))
                stack.enter_context(mock.patch.object(RUNNER, "verify_sidecar_assets"))
                stack.enter_context(mock.patch.object(RUNNER, "_dependency_probe", return_value=True))
                stack.enter_context(mock.patch.object(RUNNER.shutil, "which", return_value="/bin/tool"))
                stack.enter_context(mock.patch.object(RUNNER.BASE, "_codex_auth_available", return_value=True))
                stack.enter_context(mock.patch.object(RUNNER.BASE, "_resolved_lean_toolchain_bin", return_value=temp))
                stack.enter_context(mock.patch.object(RUNNER, "_build_frozen_lean_entry"))
                stack.enter_context(
                    mock.patch.object(
                        RUNNER,
                        "safe_preflight",
                        side_effect=lambda *_args: order.append("preflight") or {},
                    )
                )
                stack.enter_context(mock.patch.object(RUNNER, "_new_run_root", return_value=temp / "run"))
                stack.enter_context(
                    mock.patch.object(
                        RUNNER,
                        "reserve_attempt",
                        side_effect=lambda *_args, **_kwargs: (
                            order.append("reserve"),
                            (_ for _ in ()).throw(ReservationReached()),
                        )[1],
                    )
                )
                with self.assertRaises(ReservationReached):
                    RUNNER.execute(
                        identity,
                        RUNNER.SPECS["entry-game-direct"],
                        condition="static",
                        seed=1729,
                        lean_checkout=temp,
                        acknowledge_model_quota=True,
                    )
        self.assertEqual(order, ["hook", "preflight", "reserve"])

    def test_check_and_dry_run_never_dispatch_execute(self) -> None:
        identity = SimpleNamespace(root=Path("/tmp/pinned-eve"), commit="5" * 40)
        common = [
            "--eve-checkout", "/tmp/pinned-eve",
            "--lean-checkout", "/tmp/clean-lean",
            "--experiment", "entry-game-direct",
            "--protocol-id", RUNNER.PROTOCOL_ID,
            "--condition", "static",
            "--experiment-seed", "1729",
        ]
        with mock.patch.object(RUNNER.BASE, "verify_checkout", return_value=identity), mock.patch.object(
            RUNNER, "check", return_value=0
        ) as check_call, mock.patch.object(RUNNER, "dry_run", return_value=0) as dry_call, mock.patch.object(
            RUNNER, "execute", return_value=99
        ) as execute_call:
            self.assertEqual(RUNNER.main([*common, "--check"]), 0)
            self.assertEqual(RUNNER.main([*common, "--dry-run"]), 0)
        check_call.assert_called_once()
        dry_call.assert_called_once()
        execute_call.assert_not_called()

    def test_wrapper_owns_post_agent_pre_evaluation_terminal_check(self) -> None:
        source = (SIDECAR_ROOT / "scripts/run_stage5b_sol_rep003_eve.py").read_text(
            encoding="utf-8"
        )
        observed = source[
            source.index("def _observed_run_agent") : source.index(
                "def _record_rollout_terminal"
            )
        ]
        self.assertLess(
            observed.index("_ORIGINAL_RUN_AGENT(self)"),
            observed.index("TERMINAL.run_terminal_checker("),
        )
        self.assertIn("Phase2Runner._run_agent = _observed_run_agent", source)

    @unittest.skipUnless(
        Path("/usr/bin/python3").is_file()
        and platform.system() == "Darwin"
        and __import__("subprocess").run(
            ["/usr/bin/python3", "-c", "import platform; print(platform.python_version())"],
            stdout=__import__("subprocess").PIPE,
            text=True,
            check=False,
        ).stdout.strip()
        == "3.9.6",
        "requires the frozen macOS isolated solver Python 3.9.6",
    )
    def test_terminal_checker_closes_post_check_candidate_mutation(self) -> None:
        with tempfile.TemporaryDirectory(prefix="sol-rep003-terminal-") as raw:
            temp = Path(raw)
            workspace = temp / "workspace"
            repo = temp / "repo"
            toolchain = temp / "toolchain"
            (workspace / "solver").mkdir(parents=True)
            (workspace / "guidance").mkdir()
            repo.mkdir()
            toolchain.mkdir()
            (repo / "lakefile.toml").write_text("name = 'terminal-test'\n")
            lake = toolchain / "lake"
            lake.write_text("#!/bin/sh\nprintf 'fake-lean-failure\\n' >&2\nexit 1\n")
            lake.chmod(0o755)
            candidate = workspace / "solver" / "Candidate.lean"
            candidate.write_text("def beforeMutation : Nat := missingBefore\n")
            checker = workspace / "STAGE5A_LEAN_CHECK.py"
            shutil.copy2(
                SIDECAR_ROOT
                / "overlay/stage5b_sol_rep003_entry_game_direct/immutable/STAGE5A_LEAN_CHECK.py",
                checker,
            )
            env = {
                **os.environ,
                "EVE_ECONCSLIB_ROOT": str(repo),
                "PATH": f"{toolchain}:{os.environ.get('PATH', '')}",
            }
            first = __import__("subprocess").run(
                ["/usr/bin/python3", str(checker)],
                cwd=workspace,
                env=env,
                stdout=__import__("subprocess").PIPE,
                stderr=__import__("subprocess").PIPE,
                check=False,
            )
            self.assertNotEqual(first.returncode, 0)
            first_hash = sha256(candidate)
            candidate.write_text("def afterMutation : Nat := missingAfter\n")
            mutated_hash = sha256(candidate)
            self.assertNotEqual(first_hash, mutated_hash)
            old_environment = os.environ.copy()
            try:
                os.environ.clear()
                os.environ.update(env)
                evidence = TERMINAL.run_terminal_checker(
                    workspace,
                    expected_checker_sha256=sha256(checker),
                )
            finally:
                os.environ.clear()
                os.environ.update(old_environment)
            self.assertEqual(evidence["terminal_checker_phase"], "post-agent-pre-evaluation")
            self.assertEqual(evidence["terminal_check_count"], 2)
            self.assertEqual(evidence["final_candidate_sha256"], mutated_hash)
            self.assertEqual(
                evidence["local_lean_checks"][-1]["candidate_sha256"], mutated_hash
            )

    def test_terminal_rejection_is_classified_not_reported_as_incomplete(self) -> None:
        rejected = {
            "event": "solver_rollout_terminal",
            "iteration": 1,
            "workspace_id": "phase2_rejected",
            "status": "RUN_FAILED_CHECK_EVIDENCE_CONTRACT",
            "check_evidence_required": True,
            "check_evidence_validated": False,
            "failure_stage": "post-agent-pre-evaluation-terminal-check",
            "failure_message": "malformed evidence",
        }
        failures = AUDITOR._validate_terminal_events([rejected], iterations=1)
        self.assertEqual(failures, [rejected])
        self.assertEqual(failures[0]["status"], "RUN_FAILED_CHECK_EVIDENCE_CONTRACT")

    def test_missing_empty_malformed_and_mismatched_checks_fail_closed(self) -> None:
        event = lean_check_event()
        AUDITOR.validate_lean_check_chain(
            [event], checker_sha256="f" * 64, final_candidate_sha256="c" * 64
        )
        with self.assertRaises(AUDITOR.AuditError):
            AUDITOR.validate_lean_check_chain([], checker_sha256="f" * 64)
        malformed = dict(event)
        malformed["exit_code"] = "1"
        malformed["event_sha256"] = AUDITOR.event_sha256(malformed)
        with self.assertRaises(AUDITOR.AuditError):
            AUDITOR.validate_lean_check_chain(
                [malformed], checker_sha256="f" * 64
            )
        with self.assertRaises(AUDITOR.AuditError):
            AUDITOR.validate_lean_check_chain(
                [event],
                checker_sha256="f" * 64,
                final_candidate_sha256="a" * 64,
            )
        with tempfile.TemporaryDirectory(prefix="sol_rep003-malformed-telemetry-") as raw:
            root = Path(raw)
            (root / "stage5a-guidance-lineage.jsonl").write_text("not-json\n")
            with self.assertRaises(AUDITOR.AuditError):
                AUDITOR._prevalidate_runtime_evidence(root)

    def test_failed_flag_without_validated_event_cannot_forge_liveness(self) -> None:
        produced = {
            "event": "optimizer_candidate_produced",
            "candidate_id": "optimizer_new",
            "candidate_guidance_sha256": "a" * 64,
            "source_iteration": 1,
            "recorded_local_lean_failures": 1,
            "failure_before_guidance_change": True,
            "check_evidence_validated": False,
            "failure_event_hashes": ["b" * 64],
        }
        admitted = {
            "event": "optimizer_population_admission",
            "candidate_id": "optimizer_new",
            "candidate_guidance_sha256": "a" * 64,
            "source_iteration": 1,
            "admitted": True,
        }
        selected = {
            "event": "working_optimizer_sampled",
            "iteration": 2,
            "sampled": [
                {"optimizer_id": "optimizer_new", "guidance_sha256": "a" * 64}
            ],
        }
        report = AUDITOR.classify_events(
            [produced, admitted, selected], condition="evolved", iterations=3
        )
        self.assertEqual(report["status"], "PRODUCED_WITHOUT_POST_FAILURE_GUIDANCE_CHANGE")
        valid = {**produced, "check_evidence_validated": True}
        report = AUDITOR.classify_events(
            [valid, admitted, selected], condition="evolved", iterations=3
        )
        self.assertEqual(report["status"], "GUIDANCE_PRODUCED_AND_SELECTED_LATER")

    def test_auditor_rejects_missing_or_drifted_clean_preflight(self) -> None:
        preflight = {
            "schema_version": "2.0.0",
            "route": "direct",
            "solver_python_invocation": "/usr/bin/python3",
            "solver_python_executable": "/Library/Developer/CommandLineTools/usr/bin/python3",
            "solver_python_version": "3.9.6",
            "checker_sha256": AUDITOR.EXPECTED_CHECKER_SHA256,
            "candidate_sha256": "a" * 64,
            "lean_exit_code": 1,
            "lean_stdout_sha256": "b" * 64,
            "lean_stderr_sha256": "c" * 64,
            "lean_stdout_bytes": 1,
            "lean_stderr_bytes": 1,
            "recorded_event_sha256": "d" * 64,
            "model_calls": 0,
            "sol_quota_consumed": 0,
            "formal_run_root_written": False,
            "formal_attempt_ledger_written": False,
            "historical_execution_state_inherited_or_written": False,
            "disposable_workspace_removed": True,
            "snapshot_contract": "durable-files-and-sqlite-logical-content-v1",
            "quiescence_barrier_passed": True,
            "formal_state_projection_unchanged": True,
            "historical_state_projection_unchanged": True,
            "formal_state_before_sha256": "e" * 64,
            "formal_state_after_sha256": "e" * 64,
            "historical_state_before_sha256": "f" * 64,
            "historical_state_after_sha256": "f" * 64,
            "quiescence": {
                name: {
                    "label": name,
                    "stable_samples_required": 3,
                    "samples_observed": 3,
                    "poll_seconds": 0.05,
                    "timeout_seconds": 30.0,
                }
                for name in (
                    "formal_before",
                    "formal_after",
                    "historical_before",
                    "historical_after",
                )
            },
        }
        launch = {
            "route": "direct",
            "clean_lean_source_commit": AUDITOR.SOURCE_COMMIT,
            "pre_reservation_hook_guard": hook_guard_evidence(),
            "safe_preflight": preflight,
        }
        AUDITOR._validate_launch_preflight(launch)
        for key, value in (
            ("model_calls", 1),
            ("formal_run_root_written", True),
            ("checker_sha256", "0" * 64),
        ):
            drifted = {**launch, "safe_preflight": {**preflight, key: value}}
            with self.assertRaises(AUDITOR.AuditError):
                AUDITOR._validate_launch_preflight(drifted)
        with self.assertRaises(AUDITOR.AuditError):
            AUDITOR._validate_launch_preflight(
                {**launch, "clean_lean_source_commit": "0" * 40}
            )
        for key, value in (
            ("model_calls", 1),
            ("project_trusted", False),
            ("idempotent_double_write_verified", False),
            ("formal_state_after_sha256", "9" * 64),
        ):
            drifted_guard = {**hook_guard_evidence(), key: value}
            with self.assertRaises(AUDITOR.AuditError):
                AUDITOR._validate_launch_preflight(
                    {**launch, "pre_reservation_hook_guard": drifted_guard}
                )

    @unittest.skipUnless(
        Path("/usr/bin/python3").is_file()
        and platform.system() == "Darwin"
        and __import__("subprocess").run(
            ["/usr/bin/python3", "-c", "import platform; print(platform.python_version())"],
            stdout=__import__("subprocess").PIPE,
            text=True,
            check=False,
        ).stdout.strip()
        == "3.9.6",
        "requires the frozen macOS isolated solver Python 3.9.6",
    )
    def test_exact_runtime_safe_preflight_records_event_without_formal_state(self) -> None:
        with tempfile.TemporaryDirectory(prefix="sol_rep003-fake-lean-") as raw:
            temp = Path(raw)
            lean_root = temp / "source"
            toolchain = temp / "toolchain"
            lean_root.mkdir()
            toolchain.mkdir()
            (lean_root / "lakefile.toml").write_text("name = 'preflight'\n")
            lake = toolchain / "lake"
            lake.write_text(
                "#!/bin/sh\nprintf 'real-lean-stdout\\n'\nprintf 'real-lean-stderr\\n' >&2\nexit 1\n"
            )
            lake.chmod(0o755)
            before = (RUNNER.RUNS_ROOT.exists(), RUNNER.ATTEMPT_LEDGER_PATH.exists())
            report = RUNNER.safe_preflight(
                RUNNER.SPECS["entry-game-direct"], lean_root, toolchain
            )
            self.assertEqual(report["solver_python_version"], "3.9.6")
            self.assertNotEqual(report["lean_exit_code"], 0)
            self.assertGreater(report["lean_stdout_bytes"], 0)
            self.assertGreater(report["lean_stderr_bytes"], 0)
            self.assertEqual(report["model_calls"], 0)
            self.assertTrue(report["disposable_workspace_removed"])
            self.assertTrue(report["formal_state_projection_unchanged"])
            self.assertTrue(report["historical_state_projection_unchanged"])
            self.assertTrue(report["quiescence_barrier_passed"])
            self.assertEqual(
                before,
                (RUNNER.RUNS_ROOT.exists(), RUNNER.ATTEMPT_LEDGER_PATH.exists()),
            )

    def test_safe_preflight_preserves_preexisting_formal_state(self) -> None:
        with tempfile.TemporaryDirectory(prefix="sol_rep003-preexisting-state-") as raw:
            temp = Path(raw)
            runs = temp / "runs"
            ledger = temp / "ledger.sqlite3"
            lean_root = temp / "source"
            toolchain = temp / "toolchain"
            runs.mkdir()
            lean_root.mkdir()
            toolchain.mkdir()
            (lean_root / "lakefile.toml").write_text("name = 'preflight'\n")
            marker = runs / "historical-marker"
            marker.write_text("preserve\n", encoding="utf-8")
            connection = sqlite3.connect(ledger)
            connection.execute("CREATE TABLE attempts (ordinal INTEGER PRIMARY KEY)")
            connection.execute("INSERT INTO attempts VALUES (1)")
            connection.commit()
            connection.close()
            lake = toolchain / "lake"
            lake.write_text("#!/bin/sh\nprintf 'lean-failure\\n'\nexit 1\n")
            lake.chmod(0o755)
            old_runs = RUNNER.RUNS_ROOT
            old_ledger = RUNNER.ATTEMPT_LEDGER_PATH
            RUNNER.RUNS_ROOT = runs
            RUNNER.ATTEMPT_LEDGER_PATH = ledger
            try:
                before = RUNNER._execution_state_snapshot(runs, ledger)
                report = RUNNER.safe_preflight(
                    RUNNER.SPECS["entry-game-direct"], lean_root, toolchain
                )
                after = RUNNER._execution_state_snapshot(runs, ledger)
            finally:
                RUNNER.RUNS_ROOT = old_runs
                RUNNER.ATTEMPT_LEDGER_PATH = old_ledger
            self.assertEqual(before, after)
            self.assertTrue(report["formal_state_projection_unchanged"])

    def test_sqlite_wal_checkpoint_does_not_change_logical_snapshot(self) -> None:
        with tempfile.TemporaryDirectory(prefix="sol-rep003-wal-") as raw:
            temp = Path(raw)
            runs = temp / "runs"
            runs.mkdir()
            ledger = temp / "ledger.sqlite3"
            connection = sqlite3.connect(ledger)
            self.assertEqual(connection.execute("PRAGMA journal_mode=WAL").fetchone()[0], "wal")
            connection.execute("CREATE TABLE attempts (ordinal INTEGER PRIMARY KEY, status TEXT)")
            connection.execute("INSERT INTO attempts VALUES (1, 'completed')")
            connection.commit()
            before = RUNNER._execution_state_snapshot(runs, ledger)
            connection.execute("PRAGMA wal_checkpoint(TRUNCATE)").fetchall()
            after_checkpoint = RUNNER._execution_state_snapshot(runs, ledger)
            self.assertEqual(before, after_checkpoint)
            connection.execute("UPDATE attempts SET status = 'failed' WHERE ordinal = 1")
            connection.commit()
            after_logical_change = RUNNER._execution_state_snapshot(runs, ledger)
            connection.close()
            self.assertNotEqual(before, after_logical_change)

    def test_projected_snapshot_detects_durable_non_sqlite_change(self) -> None:
        with tempfile.TemporaryDirectory(prefix="sol-rep003-projection-") as raw:
            root = Path(raw)
            marker = root / "marker.json"
            marker.write_text("one\n", encoding="utf-8")
            before = RUNNER._projected_filesystem_sha256(root)
            marker.write_text("two\n", encoding="utf-8")
            self.assertNotEqual(before, RUNNER._projected_filesystem_sha256(root))

    def test_quiescence_barrier_settles_and_fails_closed(self) -> None:
        values = iter(({"state": 1}, {"state": 2}, {"state": 2}, {"state": 2}))
        snapshot, evidence = RUNNER._wait_for_quiescent_snapshot(
            lambda: next(values),
            label="settling-test",
            stable_samples=3,
            poll_seconds=0,
            timeout_seconds=1,
        )
        self.assertEqual(snapshot, {"state": 2})
        self.assertEqual(evidence["samples_observed"], 4)
        counter = {"value": 0}

        def changing_snapshot():
            counter["value"] += 1
            return {"state": counter["value"]}

        with self.assertRaises(RUNNER.CheckError):
            RUNNER._wait_for_quiescent_snapshot(
                changing_snapshot,
                label="never-stable-test",
                stable_samples=3,
                poll_seconds=0,
                timeout_seconds=0.001,
            )

    def test_fresh_sol_rep003_ledger_and_order_do_not_accept_dev002_identity(self) -> None:
        compute = self.protocol["shared_compute"]
        self.assertEqual(
            compute["fresh_run_root_parent"],
            "experiments/eve/.runtime/stage5b-sol-rep003-runs",
        )
        self.assertEqual(
            compute["durable_attempt_ledger"],
            "experiments/eve/.runtime/stage5b-sol-rep003-attempt-ledger.sqlite3",
        )
        self.assertNotIn("dev002", str(RUNNER.RUNS_ROOT).lower())
        with tempfile.TemporaryDirectory(prefix="sol_rep003-ledger-") as raw:
            temp = Path(raw)
            out_of_order = temp / "order.sqlite3"
            with self.assertRaises(RUNNER.CheckError):
                RUNNER.reserve_attempt(
                    self.protocol,
                    task="entry-game-direct",
                    condition="evolved",
                    seed=1729,
                    run_root=temp / "wrong",
                    ledger_path=out_of_order,
                )
            legacy = temp / "legacy.sqlite3"
            connection = sqlite3.connect(legacy)
            connection.execute("CREATE TABLE protocol_meta (key TEXT PRIMARY KEY, value TEXT)")
            connection.executemany(
                "INSERT INTO protocol_meta VALUES (?, ?)",
                [("protocol_id", "EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-002"), ("protocol_sha256", "0" * 64)],
            )
            connection.execute(
                "CREATE TABLE attempts (ordinal INTEGER PRIMARY KEY, task TEXT, seed INTEGER, condition TEXT, run_root TEXT UNIQUE, reserved_at TEXT, status TEXT, exit_code INTEGER, UNIQUE(task, seed, condition))"
            )
            connection.commit()
            connection.close()
            with self.assertRaises(RUNNER.CheckError):
                RUNNER.reserve_attempt(
                    self.protocol,
                    task="entry-game-direct",
                    condition="static",
                    seed=1729,
                    run_root=temp / "fresh",
                    ledger_path=legacy,
                )

    def test_hook_guard_and_preflight_precede_formal_root_and_reservation(self) -> None:
        source = (SIDECAR_ROOT / "scripts/run_stage5b_sol_rep003.py").read_text(
            encoding="utf-8"
        )
        execute_source = source[source.index("def execute(") : source.index("def _parser(")]
        self.assertLess(
            execute_source.index("pre_reservation_hook_guard("),
            execute_source.index("verify_protocol_assets("),
        )
        self.assertLess(
            execute_source.index("pre_reservation_hook_guard("),
            execute_source.index("_new_run_root("),
        )
        self.assertLess(
            execute_source.index("pre_reservation_hook_guard("),
            execute_source.index("reserve_attempt("),
        )
        self.assertLess(execute_source.index("safe_preflight("), execute_source.index("_new_run_root("))
        self.assertLess(execute_source.index("safe_preflight("), execute_source.index("reserve_attempt("))
        self.assertNotIn("stage5a-dev002-attempt-ledger", execute_source)
        self.assertNotIn("stage5a-dev002-runs", execute_source)

    def test_protocol_stops_frozen_without_execution_authorization(self) -> None:
        self.assertEqual(self.protocol["status"], "FROZEN_NOT_YET_EXECUTED")
        self.assertEqual(self.protocol["review"]["kind"], "codex-ai-review")
        self.assertFalse(self.protocol["review"]["independent_human_review"])
        boundary = self.protocol["claim_boundary"]
        self.assertIn("zero Sol REP-003 model calls", boundary)
        self.assertIn("separate explicit model/quota authorization", boundary)
        self.assertIn("Sol REP-003 execution and model/quota consumption are not authorized", boundary)
        for excluded in (
            "No REP-003 outcome",
            "complete replication",
            "causal EvE effect",
            "model capability",
            "benchmark readiness",
            "evaluation completion",
            "independent human review",
        ):
            self.assertIn(excluded, boundary)


if __name__ == "__main__":
    unittest.main()
