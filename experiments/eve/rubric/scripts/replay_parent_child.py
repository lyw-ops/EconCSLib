#!/usr/bin/env python3
"""Replay R000/R001 on the 14-candidate public corpus without model execution."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


SCRIPT_ROOT = Path(__file__).resolve().parent
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

from compare_rubrics import compare_rubrics  # noqa: E402
from r001_common import (  # noqa: E402
    R001_PATH,
    child_from_parent_result,
    child_result_errors,
    harden_obligations,
    legacy_projection,
    load_contracts,
    obligation_packet_errors,
    output_noise_errors,
)
from replay_stage2_public import _tree_snapshot, replay as replay_parent  # noqa: E402
from rubric_common import (  # noqa: E402
    R000_PATH,
    REPO_ROOT,
    RUBRIC_ROOT,
    canonical_json_bytes,
    load_json,
    prerequisite_consistency_errors,
    sha256_bytes,
    sha256_file,
    validate_instance,
)


REPORT_JSON = RUBRIC_ROOT / "reports" / "R001_PARENT_CHILD_REPLAY.json"
REPORT_MD = RUBRIC_ROOT / "reports" / "R001_PARENT_CHILD_REPLAY.md"


def _tracked_eve_paths() -> list[str]:
    completed = subprocess.run(
        ["git", "ls-files", "--", "experiments/eve"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    prefixes = (
        "experiments/eve/stage2_entry_game/",
        "experiments/eve/stage3_review/",
        "experiments/eve/stage4",
        "experiments/eve/stage5a_",
        "experiments/eve/stage5b_",
    )
    exact = {
        "experiments/eve/HANDOFF.md",
        "experiments/eve/READINESS.md",
        "experiments/eve/NEXT_SESSION_PROMPT.txt",
        "experiments/eve/scripts/evaluate_stage2_entry_game.py",
        "experiments/eve/scripts/evaluator_common.py",
    }
    return sorted(
        path for path in completed.stdout.splitlines()
        if path in exact or path.startswith(prefixes)
    )


def _snapshot(paths: list[str]) -> dict[str, str]:
    return {path: sha256_file(REPO_ROOT / path) for path in paths}


def _r000_paths() -> list[str]:
    paths = [
        path.relative_to(REPO_ROOT).as_posix()
        for directory in (RUBRIC_ROOT / "versions", RUBRIC_ROOT / "reports")
        for path in directory.glob("R000*")
        if path.is_file()
    ]
    return sorted(paths)


def _comparison(parent_result: dict[str, Any], child_result: dict[str, Any]) -> dict[str, Any]:
    parent_projection = canonical_json_bytes(legacy_projection(parent_result))
    child_projection = canonical_json_bytes(legacy_projection(child_result))
    parent_score = canonical_json_bytes(parent_result["shadow_search_score"])
    child_score = canonical_json_bytes(child_result["shadow_search_score"])
    return {
        "candidate_id": parent_result["candidate_id"],
        "route": parent_result["route"],
        "parent_hard_accepted": parent_result["hard_oracle"]["hard_accepted"],
        "child_hard_accepted": child_result["hard_oracle"]["hard_accepted"],
        "hard_decision_equal": (
            parent_result["hard_oracle"]["hard_accepted"]
            == child_result["hard_oracle"]["hard_accepted"]
        ),
        "failure_codes_equal": (
            parent_result["hard_oracle"]["failure_codes"]
            == child_result["hard_oracle"]["failure_codes"]
        ),
        "parent_shadow_search_score": parent_result["shadow_search_score"],
        "child_shadow_search_score": child_result["shadow_search_score"],
        "scalar_score_bytes_equal": parent_score == child_score,
        "parent_projection_sha256": sha256_bytes(parent_projection),
        "child_projection_sha256": sha256_bytes(child_projection),
        "projection_bytes_equal": parent_projection == child_projection,
    }


def replay(
    parent_path: Path = R000_PATH,
    child_path: Path = R001_PATH,
    *,
    verify: bool = False,
    write_reports: bool = False,
) -> dict[str, Any]:
    parent, child = load_contracts(parent_path, child_path)
    static_comparison = compare_rubrics(parent_path, child_path)
    if static_comparison["status"] != "passed":
        raise ValueError(f"parent-child contract comparison failed: {static_comparison['errors']}")

    protected_paths = _tracked_eve_paths()
    r000_paths = _r000_paths()
    historical_before = _snapshot(protected_paths)
    r000_before = _snapshot(r000_paths)
    runtime_root = REPO_ROOT / "experiments" / "eve" / ".runtime"
    runtime_before = _tree_snapshot(runtime_root)

    parent_report = replay_parent(parent_path, verify=True, write_reports=False)
    parent_results = parent_report["accepted_results"] + parent_report["mutation_results"]
    child_results = [
        child_from_parent_result(result, parent, child) for result in parent_results
    ]
    child_accepted = child_results[: len(parent_report["accepted_results"])]
    child_mutations = child_results[len(parent_report["accepted_results"]):]

    paired_context: dict[str, dict[str, Any]] = {}
    for result in child_accepted:
        paired_context.update({
            obligation["criterion_id"]: obligation
            for obligation in result["obligations"]
            if obligation["status"] != "NOT_APPLICABLE"
        })
    child_paired = harden_obligations(
        parent_report["paired_obligations"],
        parent,
        paired=True,
        context=paired_context,
    )
    paired_packet_errors = obligation_packet_errors(
        child_paired,
        parent,
        path="$child_paired_obligations",
        context=paired_context,
    )
    paired_prerequisite_errors = prerequisite_consistency_errors(
        parent,
        {**paired_context, **{
            item["criterion_id"]: item for item in child_paired
        }},
        criterion_ids={
            "PAIRED.SAME_SOURCE_LOCK",
            "PAIRED.SAME_MATHEMATICAL_TARGET",
            "PAIRED.INDEPENDENT_WORKSPACES",
            "PAIRED.ROUTE_AGREEMENT",
        },
    )
    child_validation_errors = [
        error
        for result in child_results
        for error in child_result_errors(result, parent)
    ] + paired_packet_errors + paired_prerequisite_errors

    comparisons = [
        _comparison(parent_result, child_result)
        for parent_result, child_result in zip(parent_results, child_results, strict=True)
    ]
    historical_after = _snapshot(protected_paths)
    r000_after = _snapshot(r000_paths)
    runtime_after = _tree_snapshot(runtime_root)
    checked_in_parent_bytes = (
        RUBRIC_ROOT / "reports" / "R000_STAGE2_REPLAY.json"
    ).read_bytes()
    regenerated_parent_bytes = canonical_json_bytes(parent_report)

    metrics = {
        "accepted_candidates_evaluated": len(child_accepted),
        "accepted_candidates_hard_accepted": sum(
            result["hard_oracle"]["hard_accepted"] for result in child_accepted
        ),
        "mutations_evaluated": len(child_mutations),
        "mutations_hard_rejected": sum(
            not result["hard_oracle"]["hard_accepted"]
            and result["hard_oracle"]["score"] == 0.0
            for result in child_mutations
        ),
        "blocking_false_accepts": sum(
            result["hard_oracle"]["hard_accepted"] for result in child_mutations
        ),
        "expected_failure_codes_preserved": parent_report["metrics"][
            "expected_failure_codes_preserved"
        ],
        "expected_failure_codes_total": parent_report["metrics"][
            "expected_failure_codes_total"
        ],
        "hard_decisions_equal": sum(item["hard_decision_equal"] for item in comparisons),
        "failure_codes_equal": sum(item["failure_codes_equal"] for item in comparisons),
        "scalar_scores_byte_equal": sum(
            item["scalar_score_bytes_equal"] for item in comparisons
        ),
        "normalized_outputs_byte_equal": sum(
            item["projection_bytes_equal"] for item in comparisons
        ),
        "evidence_packets_validated": sum(
            len(result["obligations"]) for result in child_results
        ) + len(child_paired),
        "evidence_packet_validation_errors": len(child_validation_errors),
    }
    invariants = {
        "r000_files_unchanged": r000_before == r000_after,
        "r000_replay_output_bytes_unchanged": checked_in_parent_bytes == regenerated_parent_bytes,
        "historical_assets_unchanged": historical_before == historical_after,
        "historical_runtime_unchanged": runtime_before == runtime_after,
        "paired_unknown_not_upgraded": all(
            item["status"] == "UNKNOWN"
            for item in child_paired
            if item["criterion_id"] in {
                "PAIRED.SAME_MATHEMATICAL_TARGET", "PAIRED.ROUTE_AGREEMENT"
            }
        ),
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
        "hard_decisions_equal": 14,
        "failure_codes_equal": 14,
        "scalar_scores_byte_equal": 14,
        "normalized_outputs_byte_equal": 14,
        "evidence_packets_validated": 494,
        "evidence_packet_validation_errors": 0,
    }
    status = "passed" if (
        metrics == expected_metrics
        and all((
            invariants["r000_files_unchanged"],
            invariants["r000_replay_output_bytes_unchanged"],
            invariants["historical_assets_unchanged"],
            invariants["historical_runtime_unchanged"],
            invariants["paired_unknown_not_upgraded"],
        ))
    ) else "failed"
    report = {
        "schema_version": "1.0.0",
        "report_id": "EVE-RUBRIC-R001-PARENT-CHILD-REPLAY",
        "rubric_id": child["rubric_id"],
        "parent_rubric_id": parent["rubric_id"],
        "status": status,
        "promotion_status": "NOT_PROMOTED",
        "corpus_semantics": [
            "public-development-corpus",
            "not-hidden-evaluation",
            "not-benchmark-generalization-evidence",
            "not-model-capability-evidence",
            "not-causal-eve-evidence",
            "codex-ai-review-not-independent-human-review",
        ],
        "parent_canonical_sha256": static_comparison["parent_canonical_sha256"],
        "child_canonical_sha256": static_comparison["child_canonical_sha256"],
        "trusted_hard_evaluator_sha256": child["trusted_acceptance_oracle"][
            "evaluator_sha256"
        ],
        "comparisons": comparisons,
        "child_accepted_results": child_accepted,
        "child_mutation_results": child_mutations,
        "child_paired_obligations": child_paired,
        "metrics": metrics,
        "invariants": invariants,
        "r000_sha256_before": r000_before,
        "r000_sha256_after": r000_after,
        "historical_protected_tree_sha256_before": sha256_bytes(
            canonical_json_bytes(historical_before)
        ),
        "historical_protected_tree_sha256_after": sha256_bytes(
            canonical_json_bytes(historical_after)
        ),
        "review": {
            "reviewer_kind": "codex-ai-review",
            "independent_human_review": False,
        },
        "limitations": [
            "This is public development-corpus replay, not hidden evaluation or benchmark generalization evidence.",
            "It is not model-capability evidence or causal EvE evidence.",
            "R001 remains NOT_PROMOTED and does not control candidate selection.",
            "Paired UNKNOWN obligations are not represented as PASS.",
            "Codex review is AI review, not independent human review.",
        ],
        "validation_errors": child_validation_errors,
    }
    schema_errors = validate_instance(
        report,
        load_json(RUBRIC_ROOT / "schemas" / "parent-child-comparison.schema.json"),
        "$report",
    )
    noise_errors = output_noise_errors(report)
    if schema_errors or noise_errors:
        report["status"] = "failed"
        report["validation_errors"].extend(schema_errors + noise_errors)
    if write_reports:
        REPORT_JSON.write_bytes(canonical_json_bytes(report))
        REPORT_MD.write_text(render_markdown(report), encoding="utf-8")
    if verify and report["status"] != "passed":
        raise RuntimeError(
            f"R001 parent-child replay failed: {metrics}, {invariants}, "
            f"errors={report['validation_errors']}"
        )
    return report


def render_markdown(report: dict[str, Any]) -> str:
    metrics = report["metrics"]
    invariants = report["invariants"]
    return f"""# R001 parent-child public replay

Status: `{report['status']}`

This is public development-corpus replay. It is not hidden evaluation,
benchmark generalization evidence, model-capability evidence, or causal EvE
evidence. R001 remains `NOT_PROMOTED`; Codex review is AI review, not
independent human review.

## Results

- Accepted evaluated / hard accepted: `{metrics['accepted_candidates_evaluated']}/{metrics['accepted_candidates_hard_accepted']}`
- Mutations evaluated / hard rejected: `{metrics['mutations_evaluated']}/{metrics['mutations_hard_rejected']}`
- Blocking false accepts: `{metrics['blocking_false_accepts']}`
- Expected failure codes preserved: `{metrics['expected_failure_codes_preserved']}/{metrics['expected_failure_codes_total']}`
- R000/R001 hard decisions equal: `{metrics['hard_decisions_equal']}/14`
- R000/R001 scalar scores byte-equal: `{metrics['scalar_scores_byte_equal']}/14`
- Normalized parent/child outputs byte-equal: `{metrics['normalized_outputs_byte_equal']}/14`
- Evidence packets validated / errors: `{metrics['evidence_packets_validated']}/{metrics['evidence_packet_validation_errors']}`
- R000 files and replay bytes unchanged: `{str(invariants['r000_files_unchanged'] and invariants['r000_replay_output_bytes_unchanged']).lower()}`
- Historical assets and `.runtime` unchanged: `{str(invariants['historical_assets_unchanged'] and invariants['historical_runtime_unchanged']).lower()}`
- Paired UNKNOWN not upgraded: `{str(invariants['paired_unknown_not_upgraded']).lower()}`
- Model calls / sessions: `0/0`
- EvE execute invocations: `0`
- Quota consumed by this task: `0`

The structured `shadow_progress_vector` is non-authoritative, uses no learned
weights, and is not connected to candidate selection.
"""


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent", type=Path, default=R000_PATH)
    parser.add_argument("--child", type=Path, default=R001_PATH)
    parser.add_argument("--verify", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        report = replay(
            args.parent,
            args.child,
            verify=args.verify,
            write_reports=True,
        )
    except (OSError, ValueError, RuntimeError) as exc:
        print(json.dumps({"status": "failed", "error": str(exc)}, indent=2, sort_keys=True))
        return 1
    print(json.dumps({
        "status": report["status"],
        "metrics": report["metrics"],
        "invariants": report["invariants"],
        "report": "experiments/eve/rubric/reports/R001_PARENT_CHILD_REPLAY.json",
    }, indent=2, sort_keys=True))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
