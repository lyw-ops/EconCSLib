#!/usr/bin/env python3
"""Fail-closed static comparison of EVE-RUBRIC-R000 and EVE-RUBRIC-R001."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


SCRIPT_ROOT = Path(__file__).resolve().parent
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

from r001_common import DELTA_PATH, R001_PATH, load_contracts  # noqa: E402
from rubric_common import (  # noqa: E402
    R000_PATH,
    RUBRIC_ROOT,
    canonical_json_bytes,
    load_json,
    sha256_bytes,
    validate_instance,
)


STABLE_ID_RE = re.compile(r"^[A-Z][A-Z0-9_]*\.[A-Z][A-Z0-9_]*$")
SEVERITY_RANK = {"P1": 1, "P2": 2, "P3": 3}


def _acyclic(criteria: list[dict[str, Any]]) -> bool:
    identifiers = {item.get("criterion_id") for item in criteria}
    outgoing = {identifier: [] for identifier in identifiers}
    indegree = {identifier: 0 for identifier in identifiers}
    for criterion in criteria:
        target = criterion.get("criterion_id")
        for source in criterion.get("prerequisites", []):
            if source not in identifiers or target not in identifiers:
                return False
            outgoing[source].append(target)
            indegree[target] += 1
    ready = sorted(identifier for identifier, degree in indegree.items() if degree == 0)
    visited = 0
    while ready:
        source = ready.pop(0)
        visited += 1
        for target in sorted(outgoing[source]):
            indegree[target] -= 1
            if indegree[target] == 0:
                ready.append(target)
                ready.sort()
    return visited == len(identifiers)


def _effective_child_criteria(
    parent: dict[str, Any], child: dict[str, Any]
) -> list[dict[str, Any]]:
    declaration = child.get("criteria")
    if declaration == {
        "mode": "inherit-byte-identical",
        "parent_path": "experiments/eve/rubric/versions/R000.json",
    }:
        return parent.get("criteria", [])
    if isinstance(declaration, list):
        return declaration
    return []


def comparison_errors(
    parent: dict[str, Any], child: dict[str, Any], delta: dict[str, Any]
) -> list[str]:
    """Return all criterion, graph, score, identity, and delta violations."""

    errors: list[str] = []
    parent_criteria = parent.get("criteria", [])
    child_criteria = _effective_child_criteria(parent, child)
    parent_by_id = {item.get("criterion_id"): item for item in parent_criteria}
    child_by_id = {item.get("criterion_id"): item for item in child_criteria}
    parent_ids = set(parent_by_id)
    child_ids = set(child_by_id)
    removed = sorted(parent_ids - child_ids)
    added = sorted(child_ids - parent_ids)
    if removed:
        errors.append(f"R000 criterion IDs removed or renamed: {removed}")
    for identifier in added:
        if not isinstance(identifier, str) or STABLE_ID_RE.fullmatch(identifier) is None:
            errors.append(f"new criterion lacks a stable ID: {identifier!r}")

    changed: list[str] = []
    for identifier in sorted(parent_ids & child_ids):
        before = parent_by_id[identifier]
        after = child_by_id[identifier]
        if before != after:
            changed.append(identifier)
        removed_prerequisites = set(before.get("prerequisites", [])) - set(
            after.get("prerequisites", [])
        )
        if removed_prerequisites:
            errors.append(
                f"{identifier}: prerequisites removed: {sorted(removed_prerequisites)}"
            )
        if (
            before.get("severity") == "P1"
            and before.get("kind") == "hard_mirror"
        ):
            if after.get("kind") != "hard_mirror":
                errors.append(f"{identifier}: P1 hard mirror kind downgraded")
            if SEVERITY_RANK.get(after.get("severity"), 99) > 1:
                errors.append(f"{identifier}: P1 severity downgraded")
            if before.get("score_role") == "fatal" and after.get("score_role") != "fatal":
                errors.append(f"{identifier}: fatal role downgraded")
            if before.get("protected") is True and after.get("protected") is not True:
                errors.append(f"{identifier}: protection downgraded")

    if not _acyclic(child_criteria):
        errors.append("child criterion DAG contains a cycle or unknown prerequisite")

    criterion_delta = delta.get("criterion_delta", {})
    declared_added = sorted(criterion_delta.get("added", []))
    declared_removed = sorted(criterion_delta.get("removed", []))
    declared_changed = sorted(criterion_delta.get("changed", []))
    if declared_added != added or declared_removed != removed or declared_changed != changed:
        errors.append("criterion changes are not exactly registered in R000_TO_R001")
    if (added or removed or changed) and not criterion_delta.get("rationale"):
        errors.append("criterion delta lacks rationale")

    child_overrides = child.get("prerequisite_overrides")
    delta_overrides = delta.get("prerequisite_overrides")
    if child_overrides != delta_overrides:
        errors.append("R001 contains an unregistered prerequisite override")
    if child_overrides != []:
        errors.append("R001 must not register prerequisite overrides")

    if child.get("parent_rubric_id") != parent.get("rubric_id"):
        errors.append("child parent_rubric_id mismatch")
    if delta.get("parent", {}).get("rubric_id") != parent.get("rubric_id"):
        errors.append("delta parent rubric ID mismatch")
    if delta.get("child", {}).get("rubric_id") != child.get("rubric_id"):
        errors.append("delta child rubric ID mismatch")
    parent_hash = sha256_bytes(canonical_json_bytes(parent))
    child_hash = sha256_bytes(canonical_json_bytes(child))
    if delta.get("parent", {}).get("canonical_sha256") != parent_hash:
        errors.append("delta parent canonical SHA-256 mismatch")
    if delta.get("child", {}).get("canonical_sha256") != child_hash:
        errors.append("delta child canonical SHA-256 mismatch")

    parent_score = parent.get("shadow_search_score", {})
    child_score = child.get("shadow_search_score", {})
    for field in ("formula_id", "maximum_rejected_score", "authoritative", "controls_selection"):
        if child_score.get(field) != parent_score.get(field):
            errors.append(f"scalar score contract changed: {field}")
    scoring_delta = delta.get("scoring_delta", {})
    if scoring_delta.get("changed") is not False:
        errors.append("scoring delta must declare no scalar change")
    if scoring_delta.get("learned_weights") is not False:
        errors.append("learned rubric weights are forbidden")
    if child.get("authoritative") is not False or child.get("controls_selection") is not False:
        errors.append("child authority/selection boundary is invalid")
    if child.get("status") != "CHILD_SHADOW_NOT_PROMOTED":
        errors.append("child is incorrectly promoted")

    graph_delta = delta.get("obligation_graph_delta", {})
    if any(graph_delta.get(field) for field in (
        "added_edges", "removed_edges", "added_nodes", "removed_nodes"
    )):
        errors.append("R001 declares an obligation graph delta despite byte inheritance")
    for section in (
        "criterion_delta", "obligation_graph_delta", "scoring_delta",
        "evidence_contract_delta", "status_delta",
    ):
        if not delta.get(section, {}).get("rationale"):
            errors.append(f"{section} lacks an explicit rationale")
    return errors


def compare_rubrics(
    parent_path: Path = R000_PATH,
    child_path: Path = R001_PATH,
    delta_path: Path = DELTA_PATH,
) -> dict[str, Any]:
    errors: list[str] = []
    try:
        parent, child = load_contracts(parent_path, child_path)
    except (OSError, ValueError) as exc:
        parent = load_json(parent_path)
        child = load_json(child_path)
        errors.append(str(exc))
    delta = load_json(delta_path)
    errors.extend(validate_instance(
        child,
        load_json(RUBRIC_ROOT / "schemas" / "r001-rubric.schema.json"),
        "$child",
    ))
    errors.extend(validate_instance(
        delta,
        load_json(RUBRIC_ROOT / "schemas" / "rubric-delta.schema.json"),
        "$delta",
    ))
    errors.extend(comparison_errors(parent, child, delta))
    return {
        "status": "passed" if not errors else "failed",
        "parent_rubric_id": parent.get("rubric_id"),
        "parent_canonical_sha256": sha256_bytes(canonical_json_bytes(parent)),
        "child_rubric_id": child.get("rubric_id"),
        "child_canonical_sha256": sha256_bytes(canonical_json_bytes(child)),
        "criteria_inherited": len(parent.get("criteria", [])),
        "criterion_delta_count": len(delta.get("criterion_delta", {}).get("changed", [])),
        "obligation_graph_delta_count": sum(len(delta.get("obligation_graph_delta", {}).get(field, [])) for field in (
            "added_edges", "removed_edges", "added_nodes", "removed_nodes"
        )),
        "scoring_delta": delta.get("scoring_delta", {}).get("changed"),
        "evidence_contract_delta_recorded": bool(
            delta.get("evidence_contract_delta", {}).get("changes")
        ),
        "errors": errors,
    }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent", type=Path, default=R000_PATH)
    parser.add_argument("--child", type=Path, default=R001_PATH)
    parser.add_argument("--delta", type=Path, default=DELTA_PATH)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    report = compare_rubrics(args.parent, args.child, args.delta)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
