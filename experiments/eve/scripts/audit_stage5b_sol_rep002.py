#!/usr/bin/env python3
"""Fail-closed read-only audit for one Stage 5B Sol REP-002 run."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import re
import sqlite3
import sys
from pathlib import Path
from typing import Any


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
RUNS_ROOT = (SIDECAR_ROOT / ".runtime" / "stage5b-sol-rep002-runs").resolve()
ATTEMPT_LEDGER_PATH = (
    SIDECAR_ROOT / ".runtime" / "stage5b-sol-rep002-attempt-ledger.sqlite3"
).resolve()
PROTOCOL_PATH = SIDECAR_ROOT / "stage5b_sol_rep002_protocol.json"
PROTOCOL_HASH_PATH = SIDECAR_ROOT / "stage5b_sol_rep002_protocol.sha256"
PROTOCOL_ID = "EVE-STAGE5B-SOL-ENTRY-GAME-GUIDANCE-LIVENESS-REP-002"
SOURCE_COMMIT = "b490317186ef435670c2eeb16050a214cdbf9fe5"
EXPECTED_PYTHON_VERSION = "3.9.6"
EXPECTED_PYTHON_INVOCATION = "/usr/bin/python3"
EXPECTED_PYTHON_EXECUTABLE = "/Library/Developer/CommandLineTools/usr/bin/python3"
EXPECTED_CHECK_COMMAND = ["lake", "env", "lean", "solver/Candidate.lean"]
EXPECTED_CHECKER_SHA256 = "65470a92468dd255879d4fe795a0ae03bb4203bd10a13191e2c1ac3bdcf89f34"
_HEX64 = re.compile(r"[0-9a-f]{64}")


def _load_legacy():
    path = SIDECAR_ROOT / "scripts" / "audit_stage5a.py"
    spec = importlib.util.spec_from_file_location("eve_stage5b_sol_rep002_audit_core", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load frozen DEV-002 auditor {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules["eve_stage5b_sol_rep002_audit_core"] = module
    spec.loader.exec_module(module)
    return module


CORE = _load_legacy()
AuditError = CORE.AuditError
CORE.RUNS_ROOT = RUNS_ROOT
CORE.ATTEMPT_LEDGER_PATH = ATTEMPT_LEDGER_PATH
CORE.PROTOCOL_PATH = PROTOCOL_PATH
CORE.PROTOCOL_HASH_PATH = PROTOCOL_HASH_PATH
CORE.PROTOCOL_ID = PROTOCOL_ID
_CORE_AUDIT_RUN = CORE.audit_run
event_sha256 = CORE.event_sha256
tree_sha256 = CORE.tree_sha256
sha256 = CORE.sha256


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and _HEX64.fullmatch(value) is not None


def validate_lean_check_chain(
    events: list[dict[str, Any]],
    *,
    checker_sha256: str,
    final_candidate_sha256: str | None = None,
) -> None:
    """Reject missing, empty, malformed, runtime-drifted, or mismatched evidence."""
    if not isinstance(events, list) or not events:
        raise AuditError("required local Lean-check evidence is missing or empty")
    previous: str | None = None
    for sequence, event in enumerate(events, start=1):
        if not isinstance(event, dict) or event.get("schema_version") != "2.0.0":
            raise AuditError("local Lean-check event schema is invalid")
        if event.get("sequence") != sequence:
            raise AuditError("local Lean-check sequence is not contiguous")
        if event.get("previous_event_sha256") != previous:
            raise AuditError("local Lean-check hash-chain predecessor mismatch")
        if event.get("checker_sha256") != checker_sha256:
            raise AuditError("local Lean check did not use the immutable checker")
        if event.get("event_sha256") != event_sha256(event):
            raise AuditError("local Lean-check event hash mismatch")
        for key in (
            "candidate_sha256",
            "guidance_sha256",
            "stdout_sha256",
            "stderr_sha256",
            "event_sha256",
        ):
            if not _is_hash(event.get(key)):
                raise AuditError(f"local Lean-check {key} is invalid")
        if event.get("python_invocation") != EXPECTED_PYTHON_INVOCATION:
            raise AuditError("local Lean-check Python invocation drifted")
        if event.get("python_executable") != EXPECTED_PYTHON_EXECUTABLE:
            raise AuditError("local Lean-check Python executable drifted")
        if event.get("python_version") != EXPECTED_PYTHON_VERSION:
            raise AuditError("local Lean-check Python version drifted")
        if event.get("command") != EXPECTED_CHECK_COMMAND:
            raise AuditError("local Lean-check command drifted")
        exit_code = event.get("exit_code")
        failed = event.get("failed")
        if isinstance(exit_code, bool) or not isinstance(exit_code, int):
            raise AuditError("local Lean-check exit status is invalid")
        if not isinstance(failed, bool) or failed != (exit_code != 0):
            raise AuditError("local Lean-check failure flag is inconsistent")
        for key in ("stdout_bytes", "stderr_bytes"):
            value = event.get(key)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise AuditError(f"local Lean-check {key} is invalid")
        try:
            instant = dt.datetime.fromisoformat(str(event.get("observed_at")))
        except ValueError as exc:
            raise AuditError("local Lean-check timestamp is malformed") from exc
        if instant.utcoffset() != dt.timedelta(0):
            raise AuditError("local Lean-check timestamp is not UTC")
        previous = str(event["event_sha256"])
    if (
        final_candidate_sha256 is not None
        and events[-1].get("candidate_sha256") != final_candidate_sha256
    ):
        raise AuditError("final local Lean-check event does not match final candidate")


def classify_events(
    events: list[dict[str, Any]], *, condition: str, iterations: int
) -> dict[str, Any]:
    """Classify liveness only from produced events carrying validated failures."""
    produced = [
        event for event in events if event.get("event") == "optimizer_candidate_produced"
    ]
    admissions = {
        str(event.get("candidate_id")): event
        for event in events
        if event.get("event") == "optimizer_population_admission"
    }
    samples = [
        event for event in events if event.get("event") == "working_optimizer_sampled"
    ]
    selected_later: list[dict[str, Any]] = []
    produced_records: list[dict[str, Any]] = []
    for event in produced:
        candidate_id = str(event.get("candidate_id"))
        candidate_hash = str(event.get("candidate_guidance_sha256"))
        source_iteration = int(event.get("source_iteration", 0))
        admission = admissions.get(candidate_id)
        admitted = bool(admission and admission.get("admitted") is True)
        later_iterations = sorted(
            int(sample.get("iteration", 0))
            for sample in samples
            if int(sample.get("iteration", 0)) > source_iteration
            and any(
                item.get("optimizer_id") == candidate_id
                and item.get("guidance_sha256") == candidate_hash
                for item in sample.get("sampled", [])
                if isinstance(item, dict)
            )
        )
        failure_hashes = event.get("failure_event_hashes")
        validated_failure = (
            event.get("check_evidence_validated") is True
            and event.get("failure_before_guidance_change") is True
            and isinstance(failure_hashes, list)
            and bool(failure_hashes)
            and all(_is_hash(value) for value in failure_hashes)
            and int(event.get("recorded_local_lean_failures", 0)) > 0
        )
        record = {
            "candidate_id": candidate_id,
            "candidate_guidance_sha256": candidate_hash,
            "source_iteration": source_iteration,
            "admitted_to_population": admitted,
            "recorded_local_lean_failures": int(
                event.get("recorded_local_lean_failures", 0)
            ),
            "failure_before_guidance_change": validated_failure,
            "has_later_opportunity": source_iteration < iterations,
            "selected_later_iterations": later_iterations,
        }
        produced_records.append(record)
        if later_iterations:
            selected_later.append(record)

    failure_derived = [
        item for item in produced_records if item["failure_before_guidance_change"]
    ]
    admitted_failure_derived = [
        item for item in failure_derived if item["admitted_to_population"]
    ]
    with_later_opportunity = [
        item for item in admitted_failure_derived if item["has_later_opportunity"]
    ]
    selected_failure_derived = [
        item for item in with_later_opportunity if item["selected_later_iterations"]
    ]
    if condition in {"static", "fixed"}:
        status = (
            "INVALID_CONTROL_GUIDANCE_RETENTION"
            if produced_records
            else "CONTROL_PASSED_NO_RETENTION"
        )
    elif not produced_records:
        status = "NO_GUIDANCE_PRODUCED"
    elif not failure_derived:
        status = "PRODUCED_WITHOUT_POST_FAILURE_GUIDANCE_CHANGE"
    elif not admitted_failure_derived:
        status = "PRODUCED_NOT_ADMITTED_TO_POPULATION"
    elif not with_later_opportunity:
        status = "PRODUCED_WITHOUT_LATER_OPPORTUNITY"
    elif not selected_failure_derived:
        status = "PRODUCED_NOT_SELECTED_LATER"
    else:
        status = "GUIDANCE_PRODUCED_AND_SELECTED_LATER"
    return {
        "status": status,
        "produced_count": len(produced_records),
        "admitted_count": sum(
            1 for item in produced_records if item["admitted_to_population"]
        ),
        "selected_later_count": len(selected_later),
        "failure_derived_selected_later_count": len(selected_failure_derived),
        "produced": produced_records,
    }


CORE.validate_lean_check_chain = validate_lean_check_chain
CORE.classify_events = classify_events


def _validate_launch_preflight(launch: dict[str, Any]) -> None:
    """Reject a launch without the frozen clean-source, zero-model preflight."""
    if launch.get("clean_lean_source_commit") != SOURCE_COMMIT:
        raise AuditError("Sol REP-002 launch clean Lean source commit drifted")
    preflight = launch.get("safe_preflight")
    if not isinstance(preflight, dict) or preflight.get("schema_version") != "2.0.0":
        raise AuditError("Sol REP-002 launch safe preflight is missing or malformed")
    if preflight.get("route") != launch.get("route"):
        raise AuditError("Sol REP-002 safe preflight route mismatch")
    expected = {
        "solver_python_invocation": EXPECTED_PYTHON_INVOCATION,
        "solver_python_executable": EXPECTED_PYTHON_EXECUTABLE,
        "solver_python_version": EXPECTED_PYTHON_VERSION,
        "checker_sha256": EXPECTED_CHECKER_SHA256,
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
    }
    for key, value in expected.items():
        if preflight.get(key) != value:
            raise AuditError(f"Sol REP-002 safe preflight {key} mismatch")
    for key in (
        "candidate_sha256",
        "lean_stdout_sha256",
        "lean_stderr_sha256",
        "recorded_event_sha256",
        "formal_state_before_sha256",
        "formal_state_after_sha256",
        "historical_state_before_sha256",
        "historical_state_after_sha256",
    ):
        if not _is_hash(preflight.get(key)):
            raise AuditError(f"Sol REP-002 safe preflight {key} is invalid")
    if preflight["formal_state_before_sha256"] != preflight["formal_state_after_sha256"]:
        raise AuditError("Sol REP-002 formal-state projection changed across preflight")
    if preflight["historical_state_before_sha256"] != preflight["historical_state_after_sha256"]:
        raise AuditError("Sol REP-002 historical-state projection changed across preflight")
    quiescence = preflight.get("quiescence")
    if not isinstance(quiescence, dict) or set(quiescence) != {
        "formal_before", "formal_after", "historical_before", "historical_after"
    }:
        raise AuditError("Sol REP-002 quiescence evidence is missing or malformed")
    for barrier in quiescence.values():
        if (
            not isinstance(barrier, dict)
            or barrier.get("stable_samples_required") != 3
            or isinstance(barrier.get("samples_observed"), bool)
            or not isinstance(barrier.get("samples_observed"), int)
            or barrier["samples_observed"] < 3
        ):
            raise AuditError("Sol REP-002 quiescence barrier evidence is invalid")
    exit_code = preflight.get("lean_exit_code")
    if isinstance(exit_code, bool) or not isinstance(exit_code, int) or exit_code == 0:
        raise AuditError("Sol REP-002 safe preflight did not record a real Lean failure")
    byte_counts = [
        preflight.get("lean_stdout_bytes"), preflight.get("lean_stderr_bytes")
    ]
    if any(
        isinstance(value, bool) or not isinstance(value, int) or value < 0
        for value in byte_counts
    ) or not any(value > 0 for value in byte_counts):
        raise AuditError("Sol REP-002 safe preflight output evidence is invalid")


def _validate_terminal_events(
    events: list[dict[str, Any]], *, iterations: int
) -> list[dict[str, Any]]:
    terminals = [
        event for event in events if event.get("event") == "solver_rollout_terminal"
    ]
    terminal_iterations = sorted(int(event.get("iteration", 0)) for event in terminals)
    if terminal_iterations != list(range(1, iterations + 1)):
        raise AuditError("Sol REP-002 terminal rollout telemetry is incomplete")
    if len({str(event.get("workspace_id")) for event in terminals}) != len(terminals):
        raise AuditError("Sol REP-002 terminal rollout workspace telemetry is duplicated")
    completed_by_iteration = {
        int(event.get("iteration", 0)): event
        for event in events
        if event.get("event") == "solver_rollout_completed"
    }
    failures: list[dict[str, Any]] = []
    for terminal in terminals:
        status = terminal.get("status")
        iteration = int(terminal.get("iteration", 0))
        if terminal.get("check_evidence_required") is not True:
            raise AuditError("Sol REP-002 terminal event did not require checker evidence")
        if status == "CHECK_EVIDENCE_VALIDATED":
            if terminal.get("check_evidence_validated") is not True:
                raise AuditError("Sol REP-002 successful terminal event lacks validated evidence")
            if terminal.get("terminal_checker_phase") != "post-agent-pre-evaluation":
                raise AuditError("Sol REP-002 terminal checker phase drifted")
            checker_hash = terminal.get("lean_checker_sha256")
            candidate_hash = terminal.get("final_candidate_sha256")
            checks = terminal.get("local_lean_checks")
            if not _is_hash(checker_hash) or not _is_hash(candidate_hash):
                raise AuditError("Sol REP-002 terminal checker or candidate hash is invalid")
            if not isinstance(checks, list):
                raise AuditError("Sol REP-002 terminal Lean-check evidence is not a list")
            validate_lean_check_chain(
                checks,
                checker_sha256=str(checker_hash),
                final_candidate_sha256=str(candidate_hash),
            )
            if terminal.get("terminal_check_event_sha256") != checks[-1].get(
                "event_sha256"
            ):
                raise AuditError("Sol REP-002 terminal checker event join drifted")
            completed = completed_by_iteration.get(iteration)
            if completed is None:
                raise AuditError("Sol REP-002 successful terminal event has no completed rollout")
            for key in (
                "workspace_id",
                "final_candidate_sha256",
                "lean_checker_sha256",
                "terminal_check_event_sha256",
            ):
                if completed.get(key) != terminal.get(key):
                    raise AuditError(f"Sol REP-002 terminal/completed {key} mismatch")
        elif status in {"RUN_FAILED_CHECK_EVIDENCE_CONTRACT", "RUN_FAILED_ROLLOUT"}:
            if status == "RUN_FAILED_CHECK_EVIDENCE_CONTRACT" and terminal.get(
                "check_evidence_validated"
            ) is not False:
                raise AuditError("Sol REP-002 rejected checker evidence was marked valid")
            if not isinstance(terminal.get("failure_stage"), str) or not isinstance(
                terminal.get("failure_message"), str
            ):
                raise AuditError("Sol REP-002 rejected terminal event lacks failure context")
            if any(
                event.get("event") == "optimizer_candidate_produced"
                and int(event.get("source_iteration", 0)) == iteration
                for event in events
            ):
                raise AuditError("Sol REP-002 rejected rollout produced an optimizer")
            failures.append(terminal)
        else:
            raise AuditError("Sol REP-002 terminal rollout status is invalid")
    return failures


def _prevalidate_runtime_evidence(
    run_root: Path,
) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]:
    launch_path = run_root.resolve() / "stage5a-launch.json"
    if not launch_path.is_file():
        raise AuditError("Sol REP-002 launch evidence is missing")
    try:
        launch = json.loads(launch_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise AuditError("Sol REP-002 launch evidence is malformed") from exc
    if not isinstance(launch, dict):
        raise AuditError("Sol REP-002 launch evidence is not an object")
    _validate_launch_preflight(launch)
    telemetry_path = run_root.resolve() / "stage5a-guidance-lineage.jsonl"
    if not telemetry_path.is_file():
        raise AuditError("Sol REP-002 telemetry evidence is missing")
    try:
        events = CORE.load_events(telemetry_path)
    except json.JSONDecodeError as exc:
        raise AuditError("Sol REP-002 telemetry evidence is malformed") from exc
    iterations = int(launch.get("iterations", 0))
    terminal_failures = _validate_terminal_events(events, iterations=iterations)
    rollouts = [
        event for event in events if event.get("event") == "solver_rollout_completed"
    ]
    workspace_ids = [str(event.get("workspace_id")) for event in rollouts]
    if len(set(workspace_ids)) != len(workspace_ids):
        raise AuditError("Sol REP-002 rollout workspace telemetry is duplicated")
    rollout_by_workspace: dict[str, dict[str, Any]] = {}
    for rollout in rollouts:
        if rollout.get("check_evidence_required") is not True:
            raise AuditError("Sol REP-002 rollout did not require Lean-check evidence")
        if rollout.get("check_evidence_validated") is not True:
            raise AuditError("Sol REP-002 rollout lacks validated Lean-check evidence")
        checker_hash = rollout.get("lean_checker_sha256")
        candidate_hash = rollout.get("final_candidate_sha256")
        checks = rollout.get("local_lean_checks")
        if not _is_hash(checker_hash) or not _is_hash(candidate_hash):
            raise AuditError("Sol REP-002 rollout checker or candidate hash is invalid")
        if not isinstance(checks, list):
            raise AuditError("Sol REP-002 local Lean-check evidence is not a list")
        validate_lean_check_chain(
            checks,
            checker_sha256=str(checker_hash),
            final_candidate_sha256=str(candidate_hash),
        )
        qualifying = [
            check
            for check in checks
            if check.get("failed") is True
            and check.get("guidance_sha256") != rollout.get("final_guidance_sha256")
        ]
        expected_sequences = [check["sequence"] for check in qualifying]
        expected_hashes = [check["event_sha256"] for check in qualifying]
        if rollout.get("failure_before_guidance_change_sequences") != expected_sequences:
            raise AuditError("Sol REP-002 failure sequence evidence drifted")
        if rollout.get("failure_event_hashes") != expected_hashes:
            raise AuditError("Sol REP-002 failure-event hashes drifted")
        rollout_by_workspace[str(rollout.get("workspace_id"))] = rollout
    for produced in (
        event for event in events if event.get("event") == "optimizer_candidate_produced"
    ):
        rollout = rollout_by_workspace.get(str(produced.get("workspace_id")))
        if rollout is None:
            raise AuditError("Sol REP-002 produced optimizer has no source rollout")
        if produced.get("check_evidence_validated") is not True:
            raise AuditError("Sol REP-002 produced optimizer lacks validated checks")
        for key in (
            "recorded_local_lean_failures",
            "failure_before_guidance_change",
            "failure_before_guidance_change_sequences",
            "failure_event_hashes",
        ):
            if produced.get(key) != rollout.get(key):
                raise AuditError(f"Sol REP-002 produced optimizer {key} mismatch")
    return launch, events, terminal_failures


def _audit_rejected_run(
    run_root: Path,
    *,
    launch: dict[str, Any],
    events: list[dict[str, Any]],
    terminal_failures: list[dict[str, Any]],
) -> dict[str, Any]:
    """Validate the run envelope when a terminal rejection replaces completion."""
    resolved = run_root.resolve()
    if resolved.parent != RUNS_ROOT or not CORE._is_relative_to(resolved, RUNS_ROOT):
        raise AuditError("run root is not one fresh Sol REP-002 run child")
    expected_protocol_hash = PROTOCOL_HASH_PATH.read_text(encoding="utf-8").split()[0]
    if sha256(PROTOCOL_PATH) != expected_protocol_hash:
        raise AuditError("detached protocol hash does not match the protocol")
    protocol = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
    if protocol.get("id") != PROTOCOL_ID or protocol.get("status") != "FROZEN_NOT_YET_EXECUTED":
        raise AuditError("frozen Sol REP-002 protocol identity or status mismatch")
    expected_launch = {
        "protocol_id": PROTOCOL_ID,
        "protocol_sha256": expected_protocol_hash,
        "protocol_status_at_launch": "FROZEN_NOT_YET_EXECUTED",
        "run_root": str(resolved),
        "status": "completed",
        "exit_code": 0,
        "resume": False,
        "import": False,
        "retry": False,
        "attempt_limit": 1,
        "attempt_reserved_before_model_access": True,
        "provider_model_seed_controlled": False,
    }
    for key, value in expected_launch.items():
        if launch.get(key) != value:
            raise AuditError(f"Sol REP-002 rejected launch {key} mismatch")
    CORE._verify_attempt_ledger(launch, protocol)
    condition = str(launch.get("condition"))
    route = str(launch.get("route"))
    experiment = str(launch.get("experiment"))
    if condition not in {"static", "fixed", "evolved"}:
        raise AuditError("Sol REP-002 rejected launch condition drifted")
    if route not in {"direct", "transport"} or experiment != f"entry-game-{route}":
        raise AuditError("Sol REP-002 rejected launch task/route mismatch")
    matrix_matches = [
        cell
        for cell in protocol.get("run_matrix", [])
        if cell.get("task") == experiment
        and cell.get("seed") == launch.get("experiment_seed")
        and cell.get("condition") == condition
    ]
    if len(matrix_matches) != 1 or launch.get("matrix_ordinal") != matrix_matches[0].get(
        "ordinal"
    ):
        raise AuditError("Sol REP-002 rejected launch matrix ordinal mismatch")
    if launch.get("solver_prompt_bundle_sha256") != protocol.get(
        "solver_prompt_bundle_hashes", {}
    ).get(route):
        raise AuditError("Sol REP-002 rejected launch prompt hash mismatch")
    guidance_key = (
        "static" if condition == "static" else f"{experiment}-fixed-and-evolved"
    )
    if launch.get("initial_guidance_tree_sha256") != protocol.get(
        "initial_guidance_tree_hashes", {}
    ).get(guidance_key):
        raise AuditError("Sol REP-002 rejected launch guidance hash mismatch")
    seed_path = resolved / "eve-stage5a-sampler-seed.json"
    if not seed_path.is_file():
        raise AuditError("Sol REP-002 rejected run sampler audit is missing")
    seed_audit = json.loads(seed_path.read_text(encoding="utf-8"))
    if (
        seed_audit.get("provider_model_seed_controlled") is not False
        or seed_audit.get("experiment_seed") != launch.get("experiment_seed")
    ):
        raise AuditError("Sol REP-002 rejected run sampler audit drifted")
    iterations = int(launch.get("iterations", 0))
    expected_iterations = list(range(1, iterations + 1))
    for event_name, message in (
        ("working_optimizer_sampled", "working optimizer selection"),
        ("solver_guidance_loaded", "solver guidance-load"),
    ):
        observed = sorted(
            int(event.get("iteration", 0))
            for event in events
            if event.get("event") == event_name
        )
        if observed != expected_iterations:
            raise AuditError(f"Sol REP-002 rejected run {message} telemetry is incomplete")
    factories = [event for event in events if event.get("event") == "factory_seeded"]
    if len(factories) != 1 or factories[0].get("provider_model_seed_controlled") is not False:
        raise AuditError("Sol REP-002 rejected run factory seed telemetry drifted")
    samples = {
        int(event.get("iteration", 0)): event
        for event in events
        if event.get("event") == "working_optimizer_sampled"
    }
    for loaded in (event for event in events if event.get("event") == "solver_guidance_loaded"):
        if loaded.get("matches_sampled_optimizer") is not True or loaded.get(
            "guidance_sha256"
        ) != loaded.get("workspace_guidance_sha256"):
            raise AuditError("Sol REP-002 rejected run loaded guidance mismatch")
        sample = samples.get(int(loaded.get("iteration", 0)))
        if sample is None or not any(
            isinstance(item, dict)
            and item.get("optimizer_id") == loaded.get("optimizer_id")
            and item.get("guidance_sha256") == loaded.get("guidance_sha256")
            for item in sample.get("sampled", [])
        ):
            raise AuditError("Sol REP-002 rejected run guidance was not sampled")
    statuses = [str(event.get("status")) for event in terminal_failures]
    status = (
        "RUN_FAILED_CHECK_EVIDENCE_CONTRACT"
        if "RUN_FAILED_CHECK_EVIDENCE_CONTRACT" in statuses
        else "RUN_FAILED_ROLLOUT"
    )
    return {
        "schema_version": "2.0.0",
        "protocol_id": PROTOCOL_ID,
        "run_root": str(resolved),
        "condition": condition,
        "status": status,
        "fresh_stage5a_root_verified": True,
        "durable_attempt_ledger_verified": True,
        "provider_model_seed_controlled": False,
        "checker_evidence_fail_closed": True,
        "terminal_rollout_events_verified": True,
        "terminal_failure_count": len(terminal_failures),
        "terminal_failures": [
            {
                "iteration": event.get("iteration"),
                "workspace_id": event.get("workspace_id"),
                "status": event.get("status"),
                "failure_stage": event.get("failure_stage"),
            }
            for event in terminal_failures
        ],
    }


def audit_run(run_root: Path) -> dict[str, Any]:
    launch, events, terminal_failures = _prevalidate_runtime_evidence(run_root)
    if terminal_failures:
        return _audit_rejected_run(
            run_root,
            launch=launch,
            events=events,
            terminal_failures=terminal_failures,
        )
    report = _CORE_AUDIT_RUN(run_root)
    report["schema_version"] = "2.0.0"
    report["checker_evidence_fail_closed"] = True
    report["terminal_rollout_events_verified"] = True
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-root", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        report = audit_run(args.run_root)
    except (AuditError, OSError, ValueError, json.JSONDecodeError, sqlite3.Error) as exc:
        print(f"Stage 5B Sol REP-002 audit error: {exc}")
        return 2
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
