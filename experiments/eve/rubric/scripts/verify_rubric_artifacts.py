#!/usr/bin/env python3
"""Verify frozen R000 hashes, schemas, graphs, replay inputs, and reports."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


SCRIPT_ROOT = Path(__file__).resolve().parent
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

from rubric_common import (  # noqa: E402
    R000_PATH,
    REPO_ROOT,
    RUBRIC_ROOT,
    canonical_json_bytes,
    load_json,
    obligation_result_validation_errors,
    prerequisite_consistency_errors,
    sha256_bytes,
    sha256_file,
    shadow_result_validation_errors,
)
from validate_rubric import validate_rubric  # noqa: E402


def verify_artifacts() -> dict[str, Any]:
    errors: list[str] = []
    validation = validate_rubric()
    errors.extend(validation["errors"])
    rubric = load_json(R000_PATH)

    detached_path = RUBRIC_ROOT / "versions" / "R000.sha256"
    detached = detached_path.read_text(encoding="utf-8").split()[0]
    normalized_hash = sha256_bytes(canonical_json_bytes(rubric))
    if detached != normalized_hash:
        errors.append("R000.sha256 does not match canonical R000 JSON")

    for source in rubric["artifact_sources"]:
        path = REPO_ROOT / source["path"]
        if not path.is_file() or sha256_file(path) != source["sha256"]:
            errors.append(f"historical source hash mismatch: {source['path']}")

    manifest = load_json(RUBRIC_ROOT / "replay" / "stage2-public-manifest.json")
    mutations = load_json(REPO_ROOT / manifest["mutations_source"])["mutations"]
    if [item["id"] for item in mutations] != manifest["expected_mutation_ids"]:
        errors.append("replay manifest mutation IDs/order do not match mutations.json")
    if len(manifest["accepted_candidates"]) != 2 or len(mutations) != 12:
        errors.append("replay manifest must cover exactly two accepted and twelve mutations")

    report_path = RUBRIC_ROOT / "reports" / "R000_STAGE2_REPLAY.json"
    if not report_path.is_file():
        errors.append("tracked Stage 2 replay JSON report is missing")
    else:
        report = load_json(report_path)
        if report.get("status") != "passed":
            errors.append("tracked Stage 2 replay report is not passed")
        accepted_results = report.get("accepted_results", [])
        mutation_results = report.get("mutation_results", [])
        mutation_expectations = report.get("mutation_expectations", [])
        paired = report.get("paired_obligations", [])
        if len(accepted_results) != 2 or len(mutation_results) != 12:
            errors.append("tracked replay must contain two accepted and twelve mutation results")
        if len(mutation_expectations) != len(mutation_results):
            errors.append("tracked replay mutation expectations do not match mutation results")
        elif [
            item.get("candidate_id") if isinstance(item, dict) else None
            for item in mutation_expectations
        ] != [
            item.get("candidate_id") if isinstance(item, dict) else None
            for item in mutation_results
        ]:
            errors.append("tracked replay mutation expectation order is malformed")
        if {
            item.get("criterion_id") for item in paired if isinstance(item, dict)
        } != {
            "PAIRED.SAME_SOURCE_LOCK",
            "PAIRED.SAME_MATHEMATICAL_TARGET",
            "PAIRED.INDEPENDENT_WORKSPACES",
            "PAIRED.ROUTE_AGREEMENT",
        }:
            errors.append("tracked replay paired obligation package is malformed")
        for group in (accepted_results, mutation_results):
            for result in group:
                errors.extend(shadow_result_validation_errors(result))
                errors.extend(prerequisite_consistency_errors(
                    rubric, result.get("obligations", [])
                ))
        errors.extend(obligation_result_validation_errors(
            paired, path="$replay.paired_obligations"
        ))
        paired_context = {
            obligation["criterion_id"]: obligation
            for result in accepted_results
            for obligation in result.get("obligations", [])
            if obligation.get("criterion_id", "").startswith(
                result.get("route", "").upper() + "."
            )
        }
        paired_context.update({
            obligation["criterion_id"]: obligation
            for obligation in paired
            if isinstance(obligation, dict) and "criterion_id" in obligation
        })
        errors.extend(prerequisite_consistency_errors(
            rubric,
            paired_context,
            criterion_ids={
                "PAIRED.SAME_SOURCE_LOCK",
                "PAIRED.SAME_MATHEMATICAL_TARGET",
                "PAIRED.INDEPENDENT_WORKSPACES",
                "PAIRED.ROUTE_AGREEMENT",
            },
        ))
    if not (RUBRIC_ROOT / "reports" / "R000_STAGE2_REPLAY.md").is_file():
        errors.append("tracked Stage 2 replay Markdown report is missing")

    return {
        "status": "passed" if not errors else "failed",
        "rubric_id": rubric["rubric_id"],
        "normalized_rubric_sha256": normalized_hash,
        "historical_sources_verified": len(rubric["artifact_sources"]),
        "errors": errors,
    }


def main() -> int:
    report = verify_artifacts()
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
