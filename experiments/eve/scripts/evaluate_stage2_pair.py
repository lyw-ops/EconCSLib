#!/usr/bin/env python3
"""Check that the two Stage 2 route reports form one valid paired result."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


SIDECAR_ROOT = Path(__file__).resolve().parent.parent
REPO_ROOT = SIDECAR_ROOT.parents[1]
TASK_ROOT = SIDECAR_ROOT / "stage2_entry_game"
TASK_ID = "EVE-ENTRY-GAME-PAIRED-001"
SOURCE_LOCK_ID = "EVE-ENTRY-GAME-SOURCE-LOCK-001"
REQUIRED_ROUTES = ("direct", "transport")
REQUIRED_GATES = {
    "boundary",
    "protected_assets_initial",
    "import_allowlist",
    "task_prefix",
    "static_guard",
    "trusted_bypass_guard",
    "route_discipline",
    "environment",
    "compile",
    "warning_policy",
    "target_declarations",
    "axiom_allowlist",
    "protected_assets_final",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"JSON root must be an object: {path}")
    return value


def evaluate_pair(direct_report_path: Path, transport_report_path: Path) -> dict[str, Any]:
    failures: list[str] = []
    reports = {
        "direct": _load(direct_report_path),
        "transport": _load(transport_report_path),
    }
    cases = {
        route: _load(TASK_ROOT / route / "case.json") for route in REQUIRED_ROUTES
    }
    source_path = TASK_ROOT / "source-lock.json"
    source_lock = _load(source_path)
    source_hash = _sha256(source_path)

    for route in REQUIRED_ROUTES:
        report = reports[route]
        case = cases[route]
        if report.get("task_id") != TASK_ID or report.get("route") != route:
            failures.append(f"{route}-report-identity-invalid")
        if report.get("status") != "passed" or report.get("score") != 1.0:
            failures.append(f"{route}-report-not-passing")
        gates = report.get("gates")
        if (
            not isinstance(gates, dict)
            or set(gates) != REQUIRED_GATES
            or not all(gates.values())
        ):
            failures.append(f"{route}-gates-not-all-passing")
        if case.get("paired_task_id") != TASK_ID or case.get("route") != route:
            failures.append(f"{route}-case-identity-invalid")
        case_source = case.get("source_lock")
        if not isinstance(case_source, dict) or case_source != {
            "id": SOURCE_LOCK_ID,
            "path": "experiments/eve/stage2_entry_game/source-lock.json",
            "sha256": source_hash,
        }:
            failures.append(f"{route}-source-lock-invalid")

    if source_lock.get("id") != SOURCE_LOCK_ID:
        failures.append("source-lock-identity-invalid")
    if source_lock.get("routes") != list(REQUIRED_ROUTES):
        failures.append("source-lock-routes-invalid")
    if cases["direct"].get("seed_candidate_sha256") == cases["transport"].get(
        "seed_candidate_sha256"
    ):
        failures.append("route-seeds-not-independent")
    if reports["direct"].get("environment") != reports["transport"].get(
        "environment"
    ):
        failures.append("route-environments-differ")

    passed = not failures
    return {
        "schema_version": "1.0.0",
        "task_id": TASK_ID,
        "status": "passed" if passed else "failed",
        "score": 1.0 if passed else 0.0,
        "failure_codes": sorted(set(failures)),
        "source_lock": {
            "id": SOURCE_LOCK_ID,
            "sha256": source_hash,
            "target": source_lock.get("interpretation", {}).get("target"),
        },
        "routes": {
            route: {
                "case_id": cases[route].get("id"),
                "report_sha256": _sha256(
                    direct_report_path if route == "direct" else transport_report_path
                ),
                "score": reports[route].get("score"),
            }
            for route in REQUIRED_ROUTES
        },
        "route_independence": {
            "separate_seed_hashes": True,
            "separate_namespaces": True,
            "cross_route_imports_allowed": False,
        },
        "review": {
            "kind": "codex-ai-review",
            "independent_human_review": False,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--direct-report", type=Path, required=True)
    parser.add_argument("--transport-report", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        report = evaluate_pair(args.direct_report, args.transport_report)
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        report = {
            "schema_version": "1.0.0",
            "task_id": TASK_ID,
            "status": "failed",
            "score": 0.0,
            "failure_codes": [f"pair-input-error:{type(exc).__name__}"],
        }
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    print(f"Stage 2 pair evaluation: {report['status']} (score={report['score']:.1f})")
    if report["failure_codes"]:
        print("Failure codes: " + ", ".join(report["failure_codes"]))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
