#!/usr/bin/env python3
"""Audit one Stage 5A run without mutating EvE state or upstream semantics."""

from __future__ import annotations

import argparse
import hashlib
import json
import sqlite3
from pathlib import Path
from typing import Any


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
RUNS_ROOT = (SIDECAR_ROOT / ".runtime" / "stage5a-dev002-runs").resolve()
ATTEMPT_LEDGER_PATH = (
    SIDECAR_ROOT / ".runtime" / "stage5a-dev002-attempt-ledger.sqlite3"
).resolve()
PROTOCOL_PATH = SIDECAR_ROOT / "stage5a_protocol.json"
PROTOCOL_HASH_PATH = SIDECAR_ROOT / "stage5a_protocol.sha256"
PROTOCOL_ID = "EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-002"


class AuditError(RuntimeError):
    pass


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(65536):
            digest.update(chunk)
    return digest.hexdigest()


def tree_sha256(files: dict[str, str]) -> str:
    digest = hashlib.sha256()
    for relative, content in sorted(files.items()):
        relative_bytes = relative.encode("utf-8")
        content_bytes = content.encode("utf-8")
        digest.update(len(relative_bytes).to_bytes(8, "big"))
        digest.update(relative_bytes)
        digest.update(len(content_bytes).to_bytes(8, "big"))
        digest.update(content_bytes)
    return digest.hexdigest()


def _is_relative_to(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def load_events(path: Path) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        value = json.loads(line)
        if not isinstance(value, dict):
            raise AuditError("Stage 5A telemetry event is not an object")
        events.append(value)
    return events


def event_sha256(event: dict[str, Any]) -> str:
    payload = {key: value for key, value in event.items() if key != "event_sha256"}
    encoded = json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def validate_lean_check_chain(
    events: list[dict[str, Any]], *, checker_sha256: str
) -> None:
    previous: str | None = None
    for sequence, event in enumerate(events, start=1):
        if event.get("sequence") != sequence:
            raise AuditError("local Lean check sequence is not contiguous")
        if event.get("previous_event_sha256") != previous:
            raise AuditError("local Lean check hash-chain predecessor mismatch")
        if event.get("checker_sha256") != checker_sha256:
            raise AuditError("local Lean check did not use the immutable checker")
        if event.get("event_sha256") != event_sha256(event):
            raise AuditError("local Lean check event hash mismatch")
        guidance_hash = event.get("guidance_sha256")
        if not isinstance(guidance_hash, str) or len(guidance_hash) != 64:
            raise AuditError("local Lean check guidance hash is missing")
        previous = str(event["event_sha256"])


def classify_events(
    events: list[dict[str, Any]], *, condition: str, iterations: int
) -> dict[str, Any]:
    produced = [event for event in events if event.get("event") == "optimizer_candidate_produced"]
    admissions = {
        str(event.get("candidate_id")): event
        for event in events
        if event.get("event") == "optimizer_population_admission"
    }
    samples = [event for event in events if event.get("event") == "working_optimizer_sampled"]
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
        record = {
            "candidate_id": candidate_id,
            "candidate_guidance_sha256": candidate_hash,
            "source_iteration": source_iteration,
            "admitted_to_population": admitted,
            "recorded_local_lean_failures": int(
                event.get("recorded_local_lean_failures", 0)
            ),
            "failure_before_guidance_change": event.get(
                "failure_before_guidance_change"
            )
            is True,
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
    failure_derived_selected_later = [
        item for item in with_later_opportunity if item["selected_later_iterations"]
    ]

    if condition in {"static", "fixed"}:
        status = (
            "INVALID_CONTROL_GUIDANCE_RETENTION"
            if produced_records or any(bool(item.get("admitted_to_population")) for item in produced_records)
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
    elif not failure_derived_selected_later:
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
        "failure_derived_selected_later_count": len(
            failure_derived_selected_later
        ),
        "produced": produced_records,
    }


def _optimizer_db_entries(run_root: Path) -> dict[str, str]:
    db_path = run_root / "optimizer_lineage.db"
    if not db_path.is_file():
        raise AuditError("optimizer_lineage.db is missing")
    connection = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
    connection.row_factory = sqlite3.Row
    try:
        rows = connection.execute(
            "SELECT entry_id, files_ref_json FROM eve_population_entries "
            "WHERE app_kind = 'eve.optimizer'"
        ).fetchall()
    finally:
        connection.close()
    entries: dict[str, str] = {}
    for row in rows:
        ref = json.loads(str(row["files_ref_json"]))
        relpath = ref.get("relpath")
        expected_file_hash = ref.get("sha256")
        if not isinstance(relpath, str) or not isinstance(expected_file_hash, str):
            raise AuditError("optimizer artifact reference is incomplete")
        artifact = (run_root / "artifacts" / relpath).resolve()
        if not _is_relative_to(artifact, (run_root / "artifacts").resolve()):
            raise AuditError("optimizer artifact escaped the current run root")
        if not artifact.is_file() or sha256(artifact) != expected_file_hash:
            raise AuditError("optimizer artifact hash mismatch")
        payload = json.loads(artifact.read_text(encoding="utf-8"))
        if not isinstance(payload, dict) or not all(
            isinstance(key, str) and isinstance(value, str)
            for key, value in payload.items()
        ):
            raise AuditError("optimizer artifact is not a text file tree")
        entries[str(row["entry_id"])] = tree_sha256(payload)
    return entries


def _verify_attempt_ledger(
    launch: dict[str, Any],
    protocol: dict[str, Any],
    *,
    ledger_path: Path | None = None,
) -> None:
    ledger_path = ATTEMPT_LEDGER_PATH if ledger_path is None else ledger_path
    if not ledger_path.is_file():
        raise AuditError("Stage 5A durable attempt ledger is missing")
    connection = sqlite3.connect(f"file:{ledger_path}?mode=ro", uri=True)
    try:
        metadata = dict(connection.execute("SELECT key, value FROM protocol_meta"))
        rows = connection.execute(
            "SELECT ordinal, task, seed, condition, run_root, status, exit_code "
            "FROM attempts ORDER BY ordinal"
        ).fetchall()
    finally:
        connection.close()
    if metadata != {
        "protocol_id": PROTOCOL_ID,
        "protocol_sha256": launch.get("protocol_sha256"),
    }:
        raise AuditError("Stage 5A attempt ledger protocol identity mismatch")
    for expected_ordinal, row in enumerate(rows, start=1):
        if expected_ordinal > len(protocol.get("run_matrix", [])):
            raise AuditError("Stage 5A attempt ledger exceeds the frozen matrix")
        cell = protocol["run_matrix"][expected_ordinal - 1]
        if row[:4] != (
            expected_ordinal,
            cell["task"],
            cell["seed"],
            cell["condition"],
        ):
            raise AuditError("Stage 5A attempt ledger order or cell identity drifted")
        if row[5] not in {"completed", "failed", "reserved"}:
            raise AuditError("Stage 5A attempt ledger has an invalid status")
        if row[5] == "reserved" and expected_ordinal != len(rows):
            raise AuditError("Stage 5A attempt ledger has a nonterminal interior row")
    launch_rows = [row for row in rows if row[0] == launch.get("matrix_ordinal")]
    expected_launch = (
        launch.get("matrix_ordinal"),
        launch.get("experiment"),
        launch.get("experiment_seed"),
        launch.get("condition"),
        launch.get("run_root"),
        "completed",
        0,
    )
    if launch_rows != [expected_launch]:
        raise AuditError("Stage 5A launch does not match its durable attempt ledger")


def audit_run(run_root: Path) -> dict[str, Any]:
    resolved = run_root.resolve()
    if resolved.parent != RUNS_ROOT or not _is_relative_to(resolved, RUNS_ROOT):
        raise AuditError("run root is not one fresh Stage 5A run child")
    launch_path = resolved / "stage5a-launch.json"
    telemetry_path = resolved / "stage5a-guidance-lineage.jsonl"
    if not launch_path.is_file() or not telemetry_path.is_file():
        raise AuditError("Stage 5A launch or telemetry evidence is missing")
    launch = json.loads(launch_path.read_text(encoding="utf-8"))
    expected_protocol_hash = PROTOCOL_HASH_PATH.read_text(encoding="utf-8").split()[0]
    if sha256(PROTOCOL_PATH) != expected_protocol_hash:
        raise AuditError("detached protocol hash does not match the protocol")
    protocol = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
    if protocol.get("id") != PROTOCOL_ID:
        raise AuditError("frozen protocol identity mismatch")
    if protocol.get("status") != "FROZEN_NOT_YET_EXECUTED":
        raise AuditError("frozen protocol status mismatch")
    if launch.get("protocol_id") != PROTOCOL_ID:
        raise AuditError("launch protocol id mismatch")
    if launch.get("protocol_sha256") != expected_protocol_hash:
        raise AuditError("launch protocol hash mismatch")
    if launch.get("run_root") != str(resolved):
        raise AuditError("launch run root mismatch")
    if launch.get("status") != "completed" or launch.get("exit_code") != 0:
        raise AuditError("run did not complete successfully")
    if launch.get("protocol_status_at_launch") != "FROZEN_NOT_YET_EXECUTED":
        raise AuditError("launch did not preserve the frozen protocol status")
    if launch.get("resume") is not False or launch.get("import") is not False:
        raise AuditError("resume/import is forbidden")
    if launch.get("attempt_limit") != 1 or launch.get("retry") is not False:
        raise AuditError("retry or multiple attempts are forbidden")
    if launch.get("attempt_reserved_before_model_access") is not True:
        raise AuditError("attempt was not reserved before model access")
    _verify_attempt_ledger(launch, protocol)
    if launch.get("provider_model_seed_controlled") is not False:
        raise AuditError("provider RNG limitation was not preserved")
    events = load_events(telemetry_path)
    iterations = int(launch.get("iterations", 0))
    condition = str(launch.get("condition"))
    route = str(launch.get("route"))
    experiment = str(launch.get("experiment"))
    if condition not in {"static", "fixed", "evolved"}:
        raise AuditError("launch condition is not frozen")
    if route not in {"direct", "transport"}:
        raise AuditError("launch route is not frozen")
    if experiment != f"entry-game-{route}":
        raise AuditError("launch task/route mismatch")
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
        raise AuditError("launch matrix ordinal does not match the frozen order")
    expected_prompt_hash = protocol.get("solver_prompt_bundle_hashes", {}).get(route)
    if launch.get("solver_prompt_bundle_sha256") != expected_prompt_hash:
        raise AuditError("launch solver prompt hash mismatch")
    guidance_key = (
        "static" if condition == "static" else f"{experiment}-fixed-and-evolved"
    )
    expected_guidance_hash = protocol.get("initial_guidance_tree_hashes", {}).get(
        guidance_key
    )
    if launch.get("initial_guidance_tree_sha256") != expected_guidance_hash:
        raise AuditError("launch initial guidance hash mismatch")
    seed_path = resolved / "eve-stage5a-sampler-seed.json"
    if not seed_path.is_file():
        raise AuditError("Stage 5A sampler seed audit is missing")
    seed_audit = json.loads(seed_path.read_text(encoding="utf-8"))
    if seed_audit.get("provider_model_seed_controlled") is not False:
        raise AuditError("sampler audit lost the provider RNG limitation")
    if seed_audit.get("experiment_seed") != launch.get("experiment_seed"):
        raise AuditError("sampler audit seed does not match launch")
    sample_iterations = sorted(
        int(event.get("iteration", 0))
        for event in events
        if event.get("event") == "working_optimizer_sampled"
    )
    if sample_iterations != list(range(1, iterations + 1)):
        raise AuditError("working optimizer selection telemetry is incomplete")
    loaded_iterations = sorted(
        int(event.get("iteration", 0))
        for event in events
        if event.get("event") == "solver_guidance_loaded"
    )
    rollout_iterations = sorted(
        int(event.get("iteration", 0))
        for event in events
        if event.get("event") == "solver_rollout_completed"
    )
    if loaded_iterations != list(range(1, iterations + 1)):
        raise AuditError("solver guidance-load telemetry is incomplete")
    if rollout_iterations != list(range(1, iterations + 1)):
        raise AuditError("solver rollout telemetry is incomplete")
    factory_events = [
        event for event in events if event.get("event") == "factory_seeded"
    ]
    if len(factory_events) != 1:
        raise AuditError("factory seed telemetry is missing or duplicated")
    if factory_events[0].get("provider_model_seed_controlled") is not False:
        raise AuditError("factory telemetry lost the provider RNG limitation")
    samples_by_iteration = {
        int(event.get("iteration", 0)): event
        for event in events
        if event.get("event") == "working_optimizer_sampled"
    }
    rollouts_by_workspace = {
        str(event.get("workspace_id")): event
        for event in events
        if event.get("event") == "solver_rollout_completed"
    }
    for event in events:
        if event.get("event") == "solver_guidance_loaded":
            if event.get("matches_sampled_optimizer") is not True:
                raise AuditError("solver guidance did not match the sampled optimizer")
            if event.get("guidance_sha256") != event.get("workspace_guidance_sha256"):
                raise AuditError("solver guidance hash mismatch")
            sample = samples_by_iteration.get(int(event.get("iteration", 0)))
            if sample is None or not any(
                item.get("optimizer_id") == event.get("optimizer_id")
                and item.get("guidance_sha256") == event.get("guidance_sha256")
                for item in sample.get("sampled", [])
                if isinstance(item, dict)
            ):
                raise AuditError("loaded solver guidance was not the sampled optimizer")
        if event.get("event") == "solver_rollout_completed":
            if event.get("lean_checker_unchanged") is not True:
                raise AuditError("immutable local Lean checker changed during rollout")
            checks = event.get("local_lean_checks")
            if not isinstance(checks, list):
                raise AuditError("local Lean check evidence is not a list")
            checker_hash = event.get("lean_checker_sha256")
            if not isinstance(checker_hash, str):
                raise AuditError("immutable local Lean checker hash is missing")
            validate_lean_check_chain(checks, checker_sha256=checker_hash)
            qualifying = [
                check
                for check in checks
                if check.get("failed") is True
                and check.get("guidance_sha256")
                != event.get("final_guidance_sha256")
            ]
            if event.get("recorded_local_lean_failures") != sum(
                check.get("failed") is True for check in checks
            ):
                raise AuditError("local Lean failure count is inconsistent")
            if event.get("failure_before_guidance_change") is not bool(qualifying):
                raise AuditError("post-failure guidance ordering evidence is inconsistent")
            if event.get("failure_before_guidance_change_sequences") != [
                check["sequence"] for check in qualifying
            ]:
                raise AuditError("post-failure guidance sequence evidence drifted")
    produced_events = {
        str(event.get("candidate_id")): event
        for event in events
        if event.get("event") == "optimizer_candidate_produced"
    }
    for candidate_id, event in produced_events.items():
        rollout = rollouts_by_workspace.get(str(event.get("workspace_id")))
        if rollout is None:
            raise AuditError("produced optimizer has no source rollout")
        if rollout.get("guidance_tree_changed") is not True:
            raise AuditError("optimizer was produced without a changed guidance tree")
        if event.get("candidate_guidance_sha256") != rollout.get(
            "final_guidance_sha256"
        ):
            raise AuditError("produced optimizer hash does not match final guidance")
        if event.get("parent_guidance_sha256") != rollout.get(
            "initial_guidance_sha256"
        ):
            raise AuditError("produced optimizer parent hash mismatch")
        if event.get("recorded_local_lean_failures") != rollout.get(
            "recorded_local_lean_failures"
        ):
            raise AuditError("produced optimizer local-failure evidence mismatch")
        if event.get("failure_before_guidance_change") != rollout.get(
            "failure_before_guidance_change"
        ):
            raise AuditError("produced optimizer failure/guidance ordering mismatch")
        if event.get("failure_before_guidance_change_sequences") != rollout.get(
            "failure_before_guidance_change_sequences"
        ):
            raise AuditError("produced optimizer failure sequence mismatch")
    db_entries = _optimizer_db_entries(resolved)
    for event in events:
        if event.get("event") != "optimizer_population_admission":
            continue
        candidate_id = str(event.get("candidate_id"))
        candidate_hash = str(event.get("candidate_guidance_sha256"))
        produced = produced_events.get(candidate_id)
        if produced is None:
            raise AuditError("population admission has no produced event")
        if produced.get("candidate_guidance_sha256") != candidate_hash:
            raise AuditError("population admission candidate hash mismatch")
        if produced.get("source_iteration") != event.get("source_iteration"):
            raise AuditError("population admission source iteration mismatch")
        if event.get("admitted") is True and db_entries.get(candidate_id) != candidate_hash:
            raise AuditError("admitted optimizer is not verifiable in lineage storage")
    classification = classify_events(
        events, condition=condition, iterations=iterations
    )
    if condition == "evolved":
        initial_ids = {
            item.get("optimizer_id")
            for event in events
            if event.get("event") == "working_optimizer_sampled"
            and int(event.get("iteration", 0)) == 1
            for item in event.get("sampled", [])
            if isinstance(item, dict)
        }
        admitted_ids = {
            event.get("candidate_id")
            for event in events
            if event.get("event") == "optimizer_population_admission"
            and event.get("admitted") is True
        }
        allowed_ids = initial_ids | admitted_ids
        for event in events:
            if event.get("event") != "working_optimizer_sampled":
                continue
            for item in event.get("sampled", []):
                if isinstance(item, dict) and item.get("optimizer_id") not in allowed_ids:
                    raise AuditError("sampled optimizer leaked from another run")
    return {
        "schema_version": "1.0.0",
        "protocol_id": PROTOCOL_ID,
        "run_root": str(resolved),
        "condition": condition,
        "fresh_stage5a_root_verified": True,
        "durable_attempt_ledger_verified": True,
        "provider_model_seed_controlled": False,
        "lineage_database_verified": True,
        **classification,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-root", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        report = audit_run(args.run_root)
    except (AuditError, OSError, ValueError, json.JSONDecodeError, sqlite3.Error) as exc:
        print(f"Stage 5A audit error: {exc}")
        return 2
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
