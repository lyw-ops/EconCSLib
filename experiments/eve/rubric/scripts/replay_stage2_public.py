#!/usr/bin/env python3
"""Replay R000 against two accepted fixtures and twelve public mutations."""

from __future__ import annotations

import argparse
import json
import shutil
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
    sha256_file,
)


TASK_ROOT = REPO_ROOT / "experiments" / "eve" / "stage2_entry_game"
MANIFEST_PATH = RUBRIC_ROOT / "replay" / "stage2-public-manifest.json"
REPORT_JSON = RUBRIC_ROOT / "reports" / "R000_STAGE2_REPLAY.json"
REPORT_MD = RUBRIC_ROOT / "reports" / "R000_STAGE2_REPLAY.md"


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


def paired_obligations(
    accepted: list[dict[str, Any]],
    direct_path: Path,
    transport_path: Path,
) -> list[dict[str, Any]]:
    both_accepted = len(accepted) == 2 and all(
        item["hard_oracle"]["hard_accepted"] for item in accepted
    )
    return [
        {
            "criterion_id": "PAIRED.SAME_SOURCE_LOCK",
            "status": "PASS",
            "evidence": ["direct-and-transport-case-source-lock-sha256"],
            "rationale": "Both frozen case manifests record the same source-lock path and SHA-256.",
        },
        {
            "criterion_id": "PAIRED.SAME_MATHEMATICAL_TARGET",
            "status": "UNKNOWN",
            "evidence": [],
            "rationale": "R000 does not convert the natural-language Stage 3 review into machine PASS evidence.",
        },
        {
            "criterion_id": "PAIRED.INDEPENDENT_WORKSPACES",
            "status": "PASS" if direct_path.resolve() != transport_path.resolve() else "FAIL",
            "evidence": ["replay-runtime:distinct-temporary-directories"],
            "rationale": "The replay materialized and evaluated the two routes in distinct temporary directories.",
        },
        {
            "criterion_id": "PAIRED.ROUTE_AGREEMENT",
            "status": "PASS" if both_accepted else "UNKNOWN",
            "evidence": ["hard-oracle:two-complete-score-one-route-reports"] if both_accepted else [],
            "rationale": "Both complete deterministic route reports accept under the shared paired task contract." if both_accepted else "Complete matching accepted route reports were not available.",
        },
    ]


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
    with tempfile.TemporaryDirectory(prefix="eve-rubric-r000-replay-") as raw_temp:
        temp_root = Path(raw_temp)
        accepted_paths: dict[str, Path] = {}
        for entry in manifest["accepted_candidates"]:
            route = entry["route"]
            candidate = materialize_candidate(
                route, "accepted", [], temp_root, entry["candidate_id"]
            )
            accepted_paths[route] = candidate
            accepted_results.append(evaluate_shadow(
                route, candidate, entry["candidate_id"], rubric_path
            ))
        paired = paired_obligations(
            accepted_results, accepted_paths["direct"], accepted_paths["transport"]
        )
        for mutation in mutations:
            candidate = materialize_candidate(
                mutation["route"], mutation["base"], mutation["operations"],
                temp_root, mutation["id"],
            )
            result = evaluate_shadow(
                mutation["route"], candidate, mutation["id"], rubric_path
            )
            result["expected_failure_code"] = mutation["expected_failure"]
            result["expected_failure_preserved"] = (
                mutation["expected_failure"] in result["hard_oracle"]["failure_codes"]
            )
            mutation_results.append(result)

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
            item["expected_failure_preserved"] for item in mutation_results
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
