#!/usr/bin/env python3
"""Fail-closed read-only audit for one Stage 5A DEV-003 run."""

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
RUNS_ROOT = (SIDECAR_ROOT / ".runtime" / "stage5a-dev003-runs").resolve()
ATTEMPT_LEDGER_PATH = (
    SIDECAR_ROOT / ".runtime" / "stage5a-dev003-attempt-ledger.sqlite3"
).resolve()
PROTOCOL_PATH = SIDECAR_ROOT / "stage5a_dev003_protocol.json"
PROTOCOL_HASH_PATH = SIDECAR_ROOT / "stage5a_dev003_protocol.sha256"
PROTOCOL_ID = "EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-003"
SOURCE_COMMIT = "b490317186ef435670c2eeb16050a214cdbf9fe5"
EXPECTED_PYTHON_VERSION = "3.9.6"
EXPECTED_PYTHON_INVOCATION = "/usr/bin/python3"
EXPECTED_PYTHON_EXECUTABLE = "/Library/Developer/CommandLineTools/usr/bin/python3"
EXPECTED_CHECK_COMMAND = ["lake", "env", "lean", "solver/Candidate.lean"]
EXPECTED_CHECKER_SHA256 = "65470a92468dd255879d4fe795a0ae03bb4203bd10a13191e2c1ac3bdcf89f34"
_HEX64 = re.compile(r"[0-9a-f]{64}")


def _load_legacy():
    path = SIDECAR_ROOT / "scripts" / "audit_stage5a.py"
    spec = importlib.util.spec_from_file_location("eve_stage5a_dev003_audit_core", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load frozen DEV-002 auditor {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules["eve_stage5a_dev003_audit_core"] = module
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
        raise AuditError("DEV-003 launch clean Lean source commit drifted")
    preflight = launch.get("safe_preflight")
    if not isinstance(preflight, dict) or preflight.get("schema_version") != "1.0.0":
        raise AuditError("DEV-003 launch safe preflight is missing or malformed")
    if preflight.get("route") != launch.get("route"):
        raise AuditError("DEV-003 safe preflight route mismatch")
    expected = {
        "solver_python_invocation": EXPECTED_PYTHON_INVOCATION,
        "solver_python_executable": EXPECTED_PYTHON_EXECUTABLE,
        "solver_python_version": EXPECTED_PYTHON_VERSION,
        "checker_sha256": EXPECTED_CHECKER_SHA256,
        "model_calls": 0,
        "luna_quota_consumed": 0,
        "formal_run_root_written": False,
        "formal_attempt_ledger_written": False,
        "dev002_execution_state_inherited_or_written": False,
        "disposable_workspace_removed": True,
        "formal_state_snapshot_unchanged": True,
        "dev002_state_snapshot_unchanged": True,
    }
    for key, value in expected.items():
        if preflight.get(key) != value:
            raise AuditError(f"DEV-003 safe preflight {key} mismatch")
    for key in (
        "candidate_sha256",
        "lean_stdout_sha256",
        "lean_stderr_sha256",
        "recorded_event_sha256",
    ):
        if not _is_hash(preflight.get(key)):
            raise AuditError(f"DEV-003 safe preflight {key} is invalid")
    exit_code = preflight.get("lean_exit_code")
    if isinstance(exit_code, bool) or not isinstance(exit_code, int) or exit_code == 0:
        raise AuditError("DEV-003 safe preflight did not record a real Lean failure")
    byte_counts = [
        preflight.get("lean_stdout_bytes"), preflight.get("lean_stderr_bytes")
    ]
    if any(
        isinstance(value, bool) or not isinstance(value, int) or value < 0
        for value in byte_counts
    ) or not any(value > 0 for value in byte_counts):
        raise AuditError("DEV-003 safe preflight output evidence is invalid")


def _prevalidate_runtime_evidence(run_root: Path) -> None:
    launch_path = run_root.resolve() / "stage5a-launch.json"
    if not launch_path.is_file():
        raise AuditError("DEV-003 launch evidence is missing")
    try:
        launch = json.loads(launch_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise AuditError("DEV-003 launch evidence is malformed") from exc
    if not isinstance(launch, dict):
        raise AuditError("DEV-003 launch evidence is not an object")
    _validate_launch_preflight(launch)
    telemetry_path = run_root.resolve() / "stage5a-guidance-lineage.jsonl"
    if not telemetry_path.is_file():
        raise AuditError("DEV-003 telemetry evidence is missing")
    try:
        events = CORE.load_events(telemetry_path)
    except json.JSONDecodeError as exc:
        raise AuditError("DEV-003 telemetry evidence is malformed") from exc
    rollouts = [
        event for event in events if event.get("event") == "solver_rollout_completed"
    ]
    workspace_ids = [str(event.get("workspace_id")) for event in rollouts]
    if len(set(workspace_ids)) != len(workspace_ids):
        raise AuditError("DEV-003 rollout workspace telemetry is duplicated")
    rollout_by_workspace: dict[str, dict[str, Any]] = {}
    for rollout in rollouts:
        if rollout.get("check_evidence_required") is not True:
            raise AuditError("DEV-003 rollout did not require Lean-check evidence")
        if rollout.get("check_evidence_validated") is not True:
            raise AuditError("DEV-003 rollout lacks validated Lean-check evidence")
        checker_hash = rollout.get("lean_checker_sha256")
        candidate_hash = rollout.get("final_candidate_sha256")
        checks = rollout.get("local_lean_checks")
        if not _is_hash(checker_hash) or not _is_hash(candidate_hash):
            raise AuditError("DEV-003 rollout checker or candidate hash is invalid")
        if not isinstance(checks, list):
            raise AuditError("DEV-003 local Lean-check evidence is not a list")
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
            raise AuditError("DEV-003 failure sequence evidence drifted")
        if rollout.get("failure_event_hashes") != expected_hashes:
            raise AuditError("DEV-003 failure-event hashes drifted")
        rollout_by_workspace[str(rollout.get("workspace_id"))] = rollout
    for produced in (
        event for event in events if event.get("event") == "optimizer_candidate_produced"
    ):
        rollout = rollout_by_workspace.get(str(produced.get("workspace_id")))
        if rollout is None:
            raise AuditError("DEV-003 produced optimizer has no source rollout")
        if produced.get("check_evidence_validated") is not True:
            raise AuditError("DEV-003 produced optimizer lacks validated checks")
        for key in (
            "recorded_local_lean_failures",
            "failure_before_guidance_change",
            "failure_before_guidance_change_sequences",
            "failure_event_hashes",
        ):
            if produced.get(key) != rollout.get(key):
                raise AuditError(f"DEV-003 produced optimizer {key} mismatch")


def audit_run(run_root: Path) -> dict[str, Any]:
    _prevalidate_runtime_evidence(run_root)
    report = _CORE_AUDIT_RUN(run_root)
    report["schema_version"] = "2.0.0"
    report["checker_evidence_fail_closed"] = True
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-root", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        report = audit_run(args.run_root)
    except (AuditError, OSError, ValueError, json.JSONDecodeError, sqlite3.Error) as exc:
        print(f"Stage 5A DEV-003 audit error: {exc}")
        return 2
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
