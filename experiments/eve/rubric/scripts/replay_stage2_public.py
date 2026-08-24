#!/usr/bin/env python3
"""Replay R000 against two accepted fixtures and twelve public mutations."""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
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
    evaluate_shadow,
    load_json,
    propagate_prerequisite_status,
    sha256_file,
    validate_obligation_results,
    validate_prerequisite_consistency,
    validate_shadow_result,
)


TASK_ROOT = REPO_ROOT / "experiments" / "eve" / "stage2_entry_game"
MANIFEST_PATH = RUBRIC_ROOT / "replay" / "stage2-public-manifest.json"
REPORT_JSON = RUBRIC_ROOT / "reports" / "R000_STAGE2_REPLAY.json"
REPORT_MD = RUBRIC_ROOT / "reports" / "R000_STAGE2_REPLAY.md"
DIRECT_CASE_PATH = TASK_ROOT / "direct" / "case.json"
TRANSPORT_CASE_PATH = TASK_ROOT / "transport" / "case.json"
PAIRED_CRITERION_IDS = (
    "PAIRED.SAME_SOURCE_LOCK",
    "PAIRED.SAME_MATHEMATICAL_TARGET",
    "PAIRED.INDEPENDENT_WORKSPACES",
    "PAIRED.ROUTE_AGREEMENT",
)


def apply_operations(source: str, route: str, operations: list[dict[str, Any]]) -> str:
    """Apply the existing Stage 2 mutation vocabulary to an in-memory source."""

    marker = f"/-! ## Solver declarations: {route} route -/"
    result = source
    for operation in operations:
        kind = operation["kind"]
        if kind == "prepend":
            result = operation["text"] + result
        elif kind == "insert_after_marker":
            if result.count(marker) != 1:
                raise ValueError("mutation marker is not unique")
            result = result.replace(marker, marker + operation["text"], 1)
        elif kind == "replace_once":
            old = operation["old"]
            if result.count(old) != 1:
                raise ValueError(f"replace_once source is not unique: {old}")
            result = result.replace(old, operation["new"], 1)
        elif kind == "replace_all":
            old = operation["old"]
            if old not in result:
                raise ValueError(f"replace_all source is absent: {old}")
            result = result.replace(old, operation["new"])
        else:
            raise ValueError(f"unknown mutation operation: {kind}")
    return result


def materialize_candidate(
    route: str,
    base: str,
    operations: list[dict[str, Any]],
    parent: Path,
    candidate_id: str,
) -> Path:
    candidate = parent / candidate_id
    shutil.copytree(TASK_ROOT / route / "seed", candidate)
    source_path = (
        TASK_ROOT / route / "seed" / "Candidate.lean"
        if base == "seed"
        else TASK_ROOT / route / "expected" / "Accepted.lean"
    )
    source = apply_operations(source_path.read_text(encoding="utf-8"), route, operations)
    (candidate / "Candidate.lean").write_text(source, encoding="utf-8")
    return candidate


def _tree_snapshot(root: Path) -> dict[str, str]:
    if not root.exists():
        return {"<state>": "absent"}
    snapshot: dict[str, str] = {"<state>": "present"}
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root).as_posix()
        if path.is_symlink():
            snapshot[relative] = f"symlink:{path.readlink()}"
        elif path.is_file():
            snapshot[relative] = sha256_file(path)
        elif path.is_dir():
            snapshot[f"{relative}/"] = "directory"
    return snapshot


def _protected_snapshot(rubric: dict[str, Any]) -> dict[str, str]:
    return {
        item["path"]: sha256_file(REPO_ROOT / item["path"])
        for item in rubric["artifact_sources"]
    }


def _obligation_result(
    criterion_id: str,
    status: str,
    evidence: list[str],
    rationale: str,
) -> dict[str, Any]:
    return {
        "criterion_id": criterion_id,
        "status": status,
        "evidence": evidence,
        "rationale": rationale,
    }


def source_lock_obligation(
    direct_case: Any,
    transport_case: Any,
    *,
    repo_root: Path = REPO_ROOT,
) -> dict[str, Any]:
    """Compare both case source locks and verify the tracked locked file."""

    criterion_id = "PAIRED.SAME_SOURCE_LOCK"
    evidence: list[str] = []
    locks: dict[str, dict[str, str]] = {}
    malformed: list[str] = []
    for label, case in (("direct-case", direct_case), ("transport-case", transport_case)):
        lock = case.get("source_lock") if isinstance(case, dict) else None
        if not isinstance(lock, dict):
            malformed.append(f"{label}:source_lock")
            continue
        normalized: dict[str, str] = {}
        for field in ("id", "path", "sha256"):
            value = lock.get(field)
            if not isinstance(value, str) or not value:
                malformed.append(f"{label}:source_lock.{field}")
                continue
            if field == "sha256" and re.fullmatch(r"[0-9a-f]{64}", value) is None:
                malformed.append(f"{label}:source_lock.sha256")
                continue
            normalized[field] = value
            evidence.append(f"{label}:source_lock.{field}={value}")
        locks[label] = normalized
    if malformed:
        return _obligation_result(
            criterion_id,
            "UNKNOWN",
            evidence + [f"malformed:{item}" for item in sorted(malformed)],
            "One or both case manifests have a missing or malformed source-lock contract.",
        )

    direct_lock = locks["direct-case"]
    transport_lock = locks["transport-case"]
    mismatched = [
        field
        for field in ("id", "path", "sha256")
        if direct_lock[field] != transport_lock[field]
    ]
    if mismatched:
        return _obligation_result(
            criterion_id,
            "FAIL",
            evidence + [f"source-lock:mismatched-field={field}" for field in mismatched],
            "The direct and transport case manifests record different source-lock identities.",
        )

    relative_path = direct_lock["path"]
    root = repo_root.resolve()
    try:
        locked_path = (root / relative_path).resolve()
        locked_path.relative_to(root)
    except (OSError, ValueError):
        return _obligation_result(
            criterion_id,
            "FAIL",
            evidence + ["source-lock:path-is-not-repository-relative"],
            "The shared source-lock path does not resolve inside the repository.",
        )
    if not locked_path.is_file():
        return _obligation_result(
            criterion_id,
            "FAIL",
            evidence + [f"source-lock:tracked-path={relative_path}"],
            "The shared source-lock path does not name an existing repository file.",
        )
    try:
        tracked = subprocess.run(
            ["git", "ls-files", "--error-unmatch", "--", relative_path],
            cwd=root,
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except OSError:
        return _obligation_result(
            criterion_id,
            "UNKNOWN",
            evidence,
            "The replay could not determine whether the shared source-lock file is tracked.",
        )
    if tracked.returncode == 1:
        return _obligation_result(
            criterion_id,
            "FAIL",
            evidence + [f"source-lock:untracked-path={relative_path}"],
            "The shared source-lock path names a file that is not tracked by Git.",
        )
    if tracked.returncode != 0:
        return _obligation_result(
            criterion_id,
            "UNKNOWN",
            evidence,
            "Git returned an unexpected result while checking the shared source-lock path.",
        )

    actual_sha256 = sha256_file(locked_path)
    evidence.extend((
        f"source-lock:tracked-path={relative_path}",
        f"source-lock:file-sha256={actual_sha256}",
    ))
    if actual_sha256 != direct_lock["sha256"]:
        return _obligation_result(
            criterion_id,
            "FAIL",
            evidence,
            "The tracked shared source-lock file does not match the manifest SHA-256.",
        )
    return _obligation_result(
        criterion_id,
        "PASS",
        evidence,
        "Both case manifests record the same source-lock identity, and its "
        "tracked file SHA-256 matches.",
    )


def paired_obligations(
    accepted: list[dict[str, Any]],
    direct_path: Path,
    transport_path: Path,
    rubric: dict[str, Any],
) -> list[dict[str, Any]]:
    by_route = {
        item["route"]: item
        for item in accepted
        if item.get("route") in ("direct", "transport")
    }
    both_accepted = set(by_route) == {"direct", "transport"} and all(
        item["hard_oracle"]["hard_accepted"] for item in by_route.values()
    )
    criteria = {item["criterion_id"]: item for item in rubric["criteria"]}
    results: dict[str, dict[str, Any]] = {}
    results["PAIRED.SAME_SOURCE_LOCK"] = source_lock_obligation(
        load_json(DIRECT_CASE_PATH), load_json(TRANSPORT_CASE_PATH)
    )
    results["PAIRED.SAME_MATHEMATICAL_TARGET"] = _obligation_result(
        "PAIRED.SAME_MATHEMATICAL_TARGET",
        "UNKNOWN",
        [],
        "R000 does not convert the natural-language Stage 3 review into machine PASS evidence.",
    )
    independent = direct_path.resolve() != transport_path.resolve()
    results["PAIRED.INDEPENDENT_WORKSPACES"] = _obligation_result(
        "PAIRED.INDEPENDENT_WORKSPACES",
        "PASS" if independent else "FAIL",
        ["replay-runtime:distinct-temporary-directories"] if independent else [],
        "The replay materialized and evaluated the two routes in distinct temporary directories."
        if independent
        else "The two accepted routes used the same materialized workspace.",
    )

    prerequisite_results: dict[str, dict[str, Any]] = {}
    for route in ("direct", "transport"):
        result = by_route.get(route)
        if result is not None:
            prerequisite_results.update({
                obligation["criterion_id"]: obligation
                for obligation in result["obligations"]
                if obligation["criterion_id"].startswith(route.upper() + ".")
            })
    prerequisite_results.update(results)
    route_agreement = _obligation_result(
        "PAIRED.ROUTE_AGREEMENT",
        "PASS" if both_accepted else "UNKNOWN",
        ["hard-oracle:two-complete-score-one-route-reports"] if both_accepted else [],
        "Both complete deterministic route reports accept under the shared paired task contract."
        if both_accepted
        else "Complete matching accepted route reports were not available.",
    )
    results["PAIRED.ROUTE_AGREEMENT"] = propagate_prerequisite_status(
        criteria["PAIRED.ROUTE_AGREEMENT"],
        prerequisite_results,
        route_agreement,
    )
    prerequisite_results.update(results)
    validate_prerequisite_consistency(
        rubric,
        prerequisite_results,
        criterion_ids=set(PAIRED_CRITERION_IDS),
    )
    paired = [results[criterion_id] for criterion_id in PAIRED_CRITERION_IDS]
    validate_obligation_results(paired, path="$paired_obligations")
    return paired


def replay(
    rubric_path: Path = R000_PATH,
    *,
    verify: bool = False,
    write_reports: bool = False,
) -> dict[str, Any]:
    rubric = load_json(rubric_path)
    manifest = load_json(MANIFEST_PATH)
    mutations_doc = load_json(REPO_ROOT / manifest["mutations_source"])
    mutations = mutations_doc["mutations"]
    expected_ids = manifest["expected_mutation_ids"]
    if [item["id"] for item in mutations] != expected_ids:
        raise ValueError("the frozen replay mutation order differs from mutations.json")

    protected_before = _protected_snapshot(rubric)
    runtime_root = REPO_ROOT / "experiments" / "eve" / ".runtime"
    runtime_before = _tree_snapshot(runtime_root)

    accepted_results: list[dict[str, Any]] = []
    mutation_results: list[dict[str, Any]] = []
    mutation_expectations: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix="eve-rubric-r000-replay-") as raw_temp:
        temp_root = Path(raw_temp)
        accepted_paths: dict[str, Path] = {}
        for entry in manifest["accepted_candidates"]:
            route = entry["route"]
            candidate = materialize_candidate(
                route, "accepted", [], temp_root, entry["candidate_id"]
            )
            accepted_paths[route] = candidate
            accepted_result = evaluate_shadow(
                route, candidate, entry["candidate_id"], rubric_path
            )
            validate_shadow_result(accepted_result)
            accepted_results.append(accepted_result)
        paired = paired_obligations(
            accepted_results,
            accepted_paths["direct"],
            accepted_paths["transport"],
            rubric,
        )
        for mutation in mutations:
            candidate = materialize_candidate(
                mutation["route"], mutation["base"], mutation["operations"],
                temp_root, mutation["id"],
            )
            result = evaluate_shadow(
                mutation["route"], candidate, mutation["id"], rubric_path
            )
            validate_shadow_result(result)
            mutation_results.append(result)
            mutation_expectations.append({
                "candidate_id": mutation["id"],
                "expected_failure_code": mutation["expected_failure"],
                "expected_failure_preserved": (
                    mutation["expected_failure"]
                    in result["hard_oracle"]["failure_codes"]
                ),
            })

    for result in accepted_results + mutation_results:
        validate_shadow_result(result)
    validate_obligation_results(paired, path="$paired_obligations")

    protected_after = _protected_snapshot(rubric)
    runtime_after = _tree_snapshot(runtime_root)
    metrics = {
        "accepted_candidates_evaluated": len(accepted_results),
        "accepted_candidates_hard_accepted": sum(
            item["hard_oracle"]["hard_accepted"] for item in accepted_results
        ),
        "mutations_evaluated": len(mutation_results),
        "mutations_hard_rejected": sum(
            not item["hard_oracle"]["hard_accepted"]
            and item["hard_oracle"]["score"] == 0.0
            for item in mutation_results
        ),
        "blocking_false_accepts": sum(
            item["hard_oracle"]["hard_accepted"] for item in mutation_results
        ),
        "expected_failure_codes_preserved": sum(
            item["expected_failure_preserved"] for item in mutation_expectations
        ),
        "expected_failure_codes_total": len(mutation_results),
    }
    invariants = {
        "historical_assets_unchanged": protected_before == protected_after,
        "historical_runtime_unchanged": runtime_before == runtime_after,
        "model_calls": 0,
        "model_sessions": 0,
        "quota_consumed_by_this_task": 0,
        "eve_execute_invocations": 0,
    }
    expected_metrics = {
        "accepted_candidates_evaluated": 2,
        "accepted_candidates_hard_accepted": 2,
        "mutations_evaluated": 12,
        "mutations_hard_rejected": 12,
        "blocking_false_accepts": 0,
        "expected_failure_codes_preserved": 12,
        "expected_failure_codes_total": 12,
    }
    status = "passed" if metrics == expected_metrics and all((
        invariants["historical_assets_unchanged"],
        invariants["historical_runtime_unchanged"],
    )) else "failed"
    report = {
        "schema_version": "1.0.0",
        "report_id": "EVE-RUBRIC-R000-STAGE2-PUBLIC-REPLAY",
        "rubric_id": rubric["rubric_id"],
        "status": status,
        "corpus_semantics": manifest["corpus_semantics"],
        "accepted_results": accepted_results,
        "mutation_results": mutation_results,
        "mutation_expectations": mutation_expectations,
        "paired_obligations": paired,
        "metrics": metrics,
        "historical_asset_sha256_before": protected_before,
        "historical_asset_sha256_after": protected_after,
        "invariants": invariants,
        "limitations": [
            "This is public development-corpus replay, not hidden evaluation or benchmark generalization evidence.",
            "It is not model-capability or causal EvE evidence.",
            "The review identity is codex-ai-review, not independent human review.",
            "DEV-003 runtime candidates are unavailable in the tracked public checkout; no trajectory replay is fabricated.",
        ],
        "review": {
            "reviewer_kind": "codex-ai-review",
            "independent_human_review": False,
        },
    }
    if verify and status != "passed":
        raise RuntimeError(f"Stage 2 public replay failed verification: {metrics}, {invariants}")
    if write_reports:
        REPORT_JSON.write_bytes(canonical_json_bytes(report))
        REPORT_MD.write_text(render_markdown(report), encoding="utf-8")
    return report


def render_markdown(report: dict[str, Any]) -> str:
    metrics = report["metrics"]
    invariants = report["invariants"]
    paired = {
        item["criterion_id"]: item["status"]
        for item in report["paired_obligations"]
    }
    return f"""# R000 Stage 2 public replay

Status: `{report['status']}`

This is a public development-corpus replay. It is not hidden evaluation,
benchmark generalization evidence, model-capability evidence, or causal EvE
evidence. The review is Codex AI review, not independent human review.

## Results

- Accepted candidates evaluated / hard accepted: `{metrics['accepted_candidates_evaluated']}/{metrics['accepted_candidates_hard_accepted']}`
- Mutations evaluated / hard rejected: `{metrics['mutations_evaluated']}/{metrics['mutations_hard_rejected']}`
- Blocking false accepts: `{metrics['blocking_false_accepts']}`
- Expected failure codes preserved: `{metrics['expected_failure_codes_preserved']}/{metrics['expected_failure_codes_total']}`
- Historical protected assets unchanged: `{str(invariants['historical_assets_unchanged']).lower()}`
- Historical `.runtime` evidence unchanged: `{str(invariants['historical_runtime_unchanged']).lower()}`
- Model calls / sessions: `0/0`
- EvE execute invocations: `0`
- Quota consumed by this task: `0`

## Paired obligations

- `PAIRED.SAME_SOURCE_LOCK`: `{paired['PAIRED.SAME_SOURCE_LOCK']}`
- `PAIRED.SAME_MATHEMATICAL_TARGET`: `{paired['PAIRED.SAME_MATHEMATICAL_TARGET']}`
- `PAIRED.INDEPENDENT_WORKSPACES`: `{paired['PAIRED.INDEPENDENT_WORKSPACES']}`
- `PAIRED.ROUTE_AGREEMENT`: `{paired['PAIRED.ROUTE_AGREEMENT']}`

## Limitation

DEV-003 runtime candidates are unavailable in the tracked public checkout;
this implementation does not fabricate trajectory replay.
"""


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rubric", type=Path, default=R000_PATH)
    parser.add_argument("--verify", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    report = replay(args.rubric, verify=args.verify, write_reports=True)
    print(json.dumps({
        "status": report["status"],
        "metrics": report["metrics"],
        "invariants": report["invariants"],
        "report": "experiments/eve/rubric/reports/R000_STAGE2_REPLAY.json",
    }, indent=2, sort_keys=True))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
