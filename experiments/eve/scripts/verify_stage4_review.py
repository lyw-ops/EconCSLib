#!/usr/bin/env python3
"""Verify the tracked Stage 4 review and, optionally, its local evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


SCRIPT_ROOT = Path(__file__).resolve().parent
SIDECAR_ROOT = SCRIPT_ROOT.parent
REPO_ROOT = SIDECAR_ROOT.parents[1]
AUDIT_PATH = SIDECAR_ROOT / "stage4_review" / "audit.json"
PROTOCOL_PATH = SIDECAR_ROOT / "stage4_protocol.json"
PROTOCOL_ID = "EVE-STAGE4-LUNA-ENTRY-GAME-DEV-002"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"expected JSON object: {path}")
    return payload


def verify(*, require_local_evidence: bool) -> dict[str, Any]:
    audit = load(AUDIT_PATH)
    protocol = load(PROTOCOL_PATH)
    if audit.get("status") != "COMPLETED_CODEX_AI_REVIEW":
        raise ValueError("Stage 4 review is not complete")
    if audit.get("protocol", {}).get("id") != PROTOCOL_ID:
        raise ValueError("Stage 4 review protocol id mismatch")
    if protocol.get("id") != PROTOCOL_ID:
        raise ValueError("Stage 4 protocol id mismatch")
    if audit["protocol"].get("sha256") != sha256(PROTOCOL_PATH):
        raise ValueError("Stage 4 protocol hash mismatch")

    machine = audit.get("machine_audit", {})
    script_path = REPO_ROOT / str(machine.get("script", ""))
    if not script_path.is_file() or sha256(script_path) != machine.get("script_sha256"):
        raise ValueError("Stage 4 audit script hash mismatch")

    cells = audit.get("cells")
    if not isinstance(cells, list) or len(cells) != 12:
        raise ValueError("Stage 4 review must contain 12 cells")
    observed = {
        (cell["task"], cell["condition"], int(cell["seed"])) for cell in cells
    }
    expected = {
        (cell["task"], cell["condition"], int(cell["seed"]))
        for cell in protocol["run_matrix"]
    }
    if observed != expected or len(observed) != 12:
        raise ValueError("Stage 4 review matrix mismatch")
    if [int(cell["ordinal"]) for cell in cells] != list(range(1, 13)):
        raise ValueError("Stage 4 review order mismatch")
    if any(len(cell.get("scores", [])) != 2 for cell in cells):
        raise ValueError("Stage 4 review candidate-count mismatch")

    execution = audit.get("execution", {})
    if execution.get("completed_unique_cells") != 12:
        raise ValueError("Stage 4 execution count mismatch")
    if execution.get("solver_candidate_instances") != 24:
        raise ValueError("Stage 4 solver count mismatch")
    if execution.get("optimizer_candidates_produced") != 0:
        raise ValueError("Stage 4 optimizer count drift")
    if audit.get("guidance_evolution", {}).get("guidance_tree_changes") != 0:
        raise ValueError("Stage 4 guidance-change count drift")
    review = audit.get("review", {})
    if review.get("independent_human_review") is not False:
        raise ValueError("Stage 4 review kind drift")
    if review.get("blocking_false_accepts") != 0:
        raise ValueError("Stage 4 false-accept count is nonzero")

    local_checked = False
    if require_local_evidence:
        local_path = REPO_ROOT / str(machine.get("local_report", ""))
        if not local_path.is_file() or sha256(local_path) != machine.get(
            "local_report_sha256"
        ):
            raise ValueError("Stage 4 local machine report is missing or changed")
        local = load(local_path)
        if local.get("audit_status") != "passed":
            raise ValueError("Stage 4 local machine audit did not pass")
        if local.get("rechecked_all_candidates") is not True:
            raise ValueError("Stage 4 local audit did not recheck all candidates")
        mapped = {
            "agent_turns": local.get("totals", {}).get("agent_turns"),
            "failed_candidate_instances": local.get("totals", {}).get(
                "failed_candidates"
            ),
            "failed_runs": local.get("totals", {}).get("failed_runs"),
            "optimizer_candidates_produced": local.get("totals", {}).get(
                "optimizer_candidates_produced"
            ),
            "output_tokens": local.get("totals", {}).get("output_tokens"),
            "passed_candidate_instances": local.get("totals", {}).get(
                "passed_candidates"
            ),
            "solver_wallclock_seconds": local.get("totals", {}).get(
                "solver_wallclock_seconds"
            ),
            "successful_runs": local.get("totals", {}).get("successful_runs"),
        }
        expected_totals = {key: execution[key] for key in mapped}
        if mapped != expected_totals:
            raise ValueError("Stage 4 local totals mismatch")
        local_checked = True

    return {
        "schema_version": "1.0.0",
        "status": "passed",
        "protocol_id": PROTOCOL_ID,
        "tracked_cells": 12,
        "candidate_instances": 24,
        "blocking_false_accepts": 0,
        "independent_human_review": False,
        "local_evidence_checked": local_checked,
    }


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--require-local-evidence", action="store_true")
    result.add_argument("--output", type=Path)
    return result


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        report = verify(require_local_evidence=args.require_local_evidence)
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(f"Stage 4 review verification failed: {exc}", file=sys.stderr)
        return 1
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
