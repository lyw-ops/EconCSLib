#!/usr/bin/env python3
"""Evidence-hardened, non-authoritative helpers for EVE-RUBRIC-R001."""

from __future__ import annotations

import copy
import re
from pathlib import Path, PurePosixPath
from typing import Any

from rubric_common import (
    FATAL_CRITERIA,
    FRONTIER_CRITERIA,
    LEGACY_EVALUATOR_PATH,
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


R001_PATH = RUBRIC_ROOT / "versions" / "R001.json"
R001_HASH_PATH = RUBRIC_ROOT / "versions" / "R001.sha256"
DELTA_PATH = RUBRIC_ROOT / "deltas" / "R000_TO_R001.json"
EVALUATOR_RELATIVE = "experiments/eve/scripts/evaluate_stage2_entry_game.py"
R001_RELATIVE = "experiments/eve/rubric/versions/R001.json"
R000_REPLAY_RELATIVE = "experiments/eve/rubric/reports/R000_STAGE2_REPLAY.json"

KNOWN_VERIFIERS = {
    "R001.LEGACY_HARD_ORACLE_REPORT_V1",
    "R001.RUBRIC_APPLICABILITY_V1",
    "R001.PAIRED_CONTRACT_V1",
}
FORBIDDEN_OUTPUT_FRAGMENTS = ("/Users/", "/private/", "\\Users\\")
TIMESTAMP_RE = re.compile(r"\b20\d\d-\d\d-\d\d[T ]\d\d:\d\d")


def _detached_hash(path: Path) -> str:
    words = path.read_text(encoding="utf-8").split()
    if not words:
        raise ValueError(f"empty detached hash: {path.name}")
    return words[0]


def _repo_path(relative: str) -> Path:
    posix = PurePosixPath(relative)
    if posix.is_absolute() or ".." in posix.parts or str(posix) != relative:
        raise ValueError(f"path is not normalized repository-relative: {relative}")
    path = (REPO_ROOT / relative).resolve()
    path.relative_to(REPO_ROOT.resolve())
    return path


def load_contracts(
    parent_path: Path = R000_PATH,
    child_path: Path = R001_PATH,
    *,
    require_child_detached_hash: bool = True,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Load R000/R001 only after exact parent and evaluator identity checks."""

    parent = load_json(parent_path)
    child = load_json(child_path)
    if parent.get("rubric_id") != "EVE-RUBRIC-R000":
        raise ValueError("parent rubric ID is not EVE-RUBRIC-R000")
    if child.get("rubric_id") != "EVE-RUBRIC-R001":
        raise ValueError("child rubric ID is not EVE-RUBRIC-R001")
    if child.get("parent_rubric_id") != parent["rubric_id"]:
        raise ValueError("R001 parent rubric ID mismatch")
    if child.get("status") != "CHILD_SHADOW_NOT_PROMOTED":
        raise ValueError("R001 promotion status is not fail-closed")
    if child.get("authoritative") is not False or child.get("controls_selection") is not False:
        raise ValueError("R001 authority boundary is invalid")

    parent_hash = sha256_bytes(canonical_json_bytes(parent))
    recorded_parent = _detached_hash(RUBRIC_ROOT / "versions" / "R000.sha256")
    declared_parent = child.get("parent_identity", {}).get("canonical_sha256")
    if parent_hash != recorded_parent or parent_hash != declared_parent:
        raise ValueError("R001 parent canonical hash mismatch")

    evaluator_hash = sha256_file(LEGACY_EVALUATOR_PATH)
    declared_evaluator = child.get("trusted_acceptance_oracle", {}).get(
        "evaluator_sha256"
    )
    parent_sources = {
        item["path"]: item["sha256"] for item in parent.get("artifact_sources", [])
    }
    if (
        evaluator_hash != declared_evaluator
        or evaluator_hash != parent_sources.get(EVALUATOR_RELATIVE)
    ):
        raise ValueError("trusted hard evaluator SHA-256 mismatch")

    if child.get("criteria") != {
        "mode": "inherit-byte-identical",
        "parent_path": "experiments/eve/rubric/versions/R000.json",
    }:
        raise ValueError("R001 criterion inheritance contract is invalid")
    if child.get("prerequisite_overrides") != []:
        raise ValueError("R001 registers an undeclared prerequisite override")

    if require_child_detached_hash:
        child_hash = sha256_bytes(canonical_json_bytes(child))
        if _detached_hash(R001_HASH_PATH) != child_hash:
            raise ValueError("R001 detached canonical hash mismatch")
    return parent, child


def criteria_by_id(parent: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {criterion["criterion_id"]: criterion for criterion in parent["criteria"]}


def _packet_source(criterion_id: str, source_kind: str) -> tuple[str, str]:
    if source_kind == "hard_oracle_report":
        relative = R000_REPLAY_RELATIVE
    elif source_kind == "paired_contract":
        relative = R000_REPLAY_RELATIVE
    else:
        relative = R001_RELATIVE
    return relative, sha256_file(_repo_path(relative))


def make_evidence_packet(
    result: dict[str, Any],
    criterion: dict[str, Any],
    all_results: dict[str, dict[str, Any]],
    *,
    source_kind: str,
    oracle_report_sha256: str | None = None,
) -> dict[str, Any]:
    """Bind one inherited result to stable source bytes and its derivation."""

    criterion_id = criterion["criterion_id"]
    relative, source_hash = _packet_source(criterion_id, source_kind)
    if source_kind == "hard_oracle_report":
        verifier_id = "R001.LEGACY_HARD_ORACLE_REPORT_V1"
    elif source_kind == "paired_contract":
        verifier_id = "R001.PAIRED_CONTRACT_V1"
    else:
        verifier_id = "R001.RUBRIC_APPLICABILITY_V1"
    strength = criterion["evidence_strength"]
    if result["status"] == "PASS" and criterion["kind"] == "hard_mirror":
        strength = "deterministic_contract"
    prerequisites = {
        prerequisite: all_results.get(prerequisite, {}).get("status", "UNKNOWN")
        for prerequisite in criterion.get("prerequisites", [])
    }
    derivation_evidence = ", ".join(result.get("evidence", [])) or "none"
    packet = {
        "criterion_id": criterion_id,
        "status": result["status"],
        "claim": criterion["description"],
        "evidence_strength": strength,
        "source_kind": source_kind,
        "source_path": relative,
        "source_sha256": source_hash,
        "verifier_id": verifier_id,
        "derivation": f"{result['rationale']} Evidence references: {derivation_evidence}.",
        "prerequisite_statuses": prerequisites,
    }
    if source_kind == "hard_oracle_report" and oracle_report_sha256 is not None:
        packet["oracle_report_sha256"] = oracle_report_sha256
        packet["derivation"] += (
            f" Hard-oracle report SHA-256: {oracle_report_sha256}."
        )
    return packet


def harden_obligations(
    obligations: list[dict[str, Any]],
    parent: dict[str, Any],
    *,
    paired: bool = False,
    context: dict[str, dict[str, Any]] | None = None,
    oracle_report_sha256: str | None = None,
) -> list[dict[str, Any]]:
    by_id = {item["criterion_id"]: item for item in obligations}
    if context:
        by_id = {**context, **by_id}
    criteria = criteria_by_id(parent)
    hardened: list[dict[str, Any]] = []
    for result in obligations:
        criterion = criteria[result["criterion_id"]]
        applies = criterion["applies_when"]
        if paired:
            source_kind = "paired_contract"
        elif result["status"] == "NOT_APPLICABLE" or applies == "paired":
            source_kind = "rubric_contract"
        else:
            source_kind = "hard_oracle_report"
        item = copy.deepcopy(result)
        item["evidence_packet"] = make_evidence_packet(
            item,
            criterion,
            by_id,
            source_kind=source_kind,
            oracle_report_sha256=oracle_report_sha256,
        )
        hardened.append(item)
    return hardened


def evidence_packet_errors(
    result: dict[str, Any],
    criterion: dict[str, Any],
    all_results: dict[str, dict[str, Any]],
    *,
    path: str,
    oracle_report_sha256: str | None = None,
) -> list[str]:
    packet = result.get("evidence_packet")
    if not isinstance(packet, dict):
        return [f"{path}: missing evidence packet"]
    schema = load_json(RUBRIC_ROOT / "schemas" / "evidence-packet.schema.json")
    errors = validate_instance(packet, schema, f"{path}.evidence_packet")
    if packet.get("criterion_id") != result.get("criterion_id"):
        errors.append(f"{path}: packet criterion ID mismatch")
    if packet.get("status") != result.get("status"):
        errors.append(f"{path}: packet status mismatch")
    if packet.get("claim") != criterion.get("description"):
        errors.append(f"{path}: packet claim mismatch")
    if packet.get("verifier_id") not in KNOWN_VERIFIERS:
        errors.append(f"{path}: unknown verifier")
    if packet.get("source_kind") == "hard_oracle_report":
        if packet.get("oracle_report_sha256") != oracle_report_sha256:
            errors.append(f"{path}: hard-oracle report SHA-256 mismatch")
    elif "oracle_report_sha256" in packet:
        errors.append(f"{path}: non-oracle packet carries oracle report SHA-256")
    relative = packet.get("source_path")
    try:
        source_path = _repo_path(relative) if isinstance(relative, str) else None
    except (OSError, ValueError):
        source_path = None
        errors.append(f"{path}: source path is not repository-relative")
    if source_path is None or not source_path.is_file():
        errors.append(f"{path}: evidence source is missing")
    elif packet.get("source_sha256") != sha256_file(source_path):
        errors.append(f"{path}: evidence source SHA-256 drift")

    expected_prerequisites = {
        prerequisite: all_results.get(prerequisite, {}).get("status", "UNKNOWN")
        for prerequisite in criterion.get("prerequisites", [])
    }
    if packet.get("prerequisite_statuses") != expected_prerequisites:
        errors.append(f"{path}: prerequisite status packet mismatch")
    if result.get("status") == "PASS":
        strength = packet.get("evidence_strength")
        if criterion.get("kind") == "semantic_progress" and strength in {
            "syntactic_only", "review_only"
        }:
            errors.append(f"{path}: semantic PASS uses insufficient evidence")
        if criterion.get("kind") == "review_only":
            errors.append(f"{path}: review-only criterion cannot be PASS")
        if strength not in {
            "lean_kernel", "deterministic_contract", "deterministic_static"
        }:
            errors.append(f"{path}: PASS lacks direct evidence strength")
    return errors


def obligation_packet_errors(
    obligations: list[dict[str, Any]],
    parent: dict[str, Any],
    *,
    path: str,
    context: dict[str, dict[str, Any]] | None = None,
    oracle_report_sha256: str | None = None,
) -> list[str]:
    criteria = criteria_by_id(parent)
    by_id = {item.get("criterion_id"): item for item in obligations}
    if context:
        by_id = {**context, **by_id}
    errors: list[str] = []
    for index, result in enumerate(obligations):
        criterion = criteria.get(result.get("criterion_id"))
        if criterion is None:
            errors.append(f"{path}[{index}]: unknown criterion")
            continue
        errors.extend(
            evidence_packet_errors(
                result,
                criterion,
                by_id,
                path=f"{path}[{index}]",
                oracle_report_sha256=oracle_report_sha256,
            )
        )
    return errors


def compute_progress_vector(
    hard_accepted: bool,
    obligations: list[dict[str, Any]],
    parent: dict[str, Any],
) -> dict[str, Any]:
    """Compute the monotone structured diagnostic without learned weights."""

    criteria = criteria_by_id(parent)
    by_id = {item["criterion_id"]: item for item in obligations}
    valid_passes: set[str] = set()
    for criterion_id, result in by_id.items():
        if result.get("status") != "PASS":
            continue
        if not evidence_packet_errors(
            result,
            criteria[criterion_id],
            by_id,
            path=f"$vector.{criterion_id}",
            oracle_report_sha256=result.get("evidence_packet", {}).get(
                "oracle_report_sha256"
            ),
        ):
            valid_passes.add(criterion_id)
    fatal_integrity = all(
        by_id.get(identifier, {}).get("status") != "FAIL"
        and identifier in valid_passes
        for identifier in FATAL_CRITERIA
    )
    core_frontier_passes = sum(
        identifier in valid_passes
        and criteria[identifier]["evidence_strength"] not in {"syntactic_only", "review_only"}
        for identifier in FRONTIER_CRITERIA
    )
    route = "direct" if any(
        item.startswith("DIRECT.") and by_id[item]["status"] != "NOT_APPLICABLE"
        for item in by_id
    ) else "transport"
    lean_kernel_route_passes = sum(
        identifier in valid_passes
        and criterion["applies_when"] == route
        and criterion["evidence_strength"] == "lean_kernel"
        for identifier, criterion in criteria.items()
    )
    deterministic_contract_route_passes = sum(
        identifier in valid_passes
        and criterion["applies_when"] == route
        and criterion["evidence_strength"] == "deterministic_contract"
        for identifier, criterion in criteria.items()
    )
    applicable = [
        result for identifier, result in by_id.items()
        if criteria[identifier]["applies_when"] in ("all", route)
    ]
    return {
        "hard_accepted": hard_accepted,
        "rank_eligible": fatal_integrity,
        "fatal_integrity": fatal_integrity,
        "core_frontier_passes": core_frontier_passes,
        "lean_kernel_route_passes": lean_kernel_route_passes,
        "deterministic_contract_route_passes": deterministic_contract_route_passes,
        "applicable_unknown_count": sum(item["status"] == "UNKNOWN" for item in applicable),
        "applicable_not_evaluated_count": sum(
            item["status"] == "NOT_EVALUATED" for item in applicable
        ),
    }


def child_from_parent_result(
    parent_result: dict[str, Any],
    parent: dict[str, Any],
    child: dict[str, Any],
) -> dict[str, Any]:
    obligations = harden_obligations(
        parent_result["obligations"],
        parent,
        oracle_report_sha256=parent_result["hard_oracle"]["report_sha256"],
    )
    result = {
        "schema_version": "1.1.0",
        "rubric_id": child["rubric_id"],
        "parent_rubric_id": parent["rubric_id"],
        "candidate_id": parent_result["candidate_id"],
        "route": parent_result["route"],
        "hard_oracle": copy.deepcopy(parent_result["hard_oracle"]),
        "obligations": obligations,
        "failure_frontier": copy.deepcopy(parent_result["failure_frontier"]),
        "shadow_search_score": parent_result["shadow_search_score"],
        "shadow_progress_vector": compute_progress_vector(
            parent_result["hard_oracle"]["hard_accepted"], obligations, parent
        ),
        "score_semantics": "non-authoritative-shadow-only",
        "controls_selection": False,
        "mathematical_acceptance": False,
        "limitations": [
            "The existing deterministic binary evaluator remains the only acceptance oracle.",
            "R001 is a non-promoted child over a public development corpus.",
            "Evidence packets and the progress vector do not control candidate selection.",
            "Syntactic-only and review-only evidence do not establish semantic PASS.",
        ],
    }
    errors = child_result_errors(result, parent)
    if errors:
        raise ValueError("R001 child result failed closed: " + "; ".join(errors))
    return result


def child_result_errors(result: dict[str, Any], parent: dict[str, Any]) -> list[str]:
    errors = validate_instance(
        result,
        load_json(RUBRIC_ROOT / "schemas" / "r001-shadow-evaluation.schema.json"),
        "$child",
    )
    obligations = result.get("obligations")
    if not isinstance(obligations, list):
        return errors + ["$child.obligations: expected list"]
    obligation_schema = load_json(
        RUBRIC_ROOT / "schemas" / "r001-obligation-result.schema.json"
    )
    for index, obligation in enumerate(obligations):
        errors.extend(validate_instance(
            obligation, obligation_schema, f"$child.obligations[{index}]"
        ))
    errors.extend(obligation_packet_errors(
        obligations,
        parent,
        path="$child.obligations",
        oracle_report_sha256=result.get("hard_oracle", {}).get("report_sha256"),
    ))
    errors.extend(prerequisite_consistency_errors(parent, obligations))
    hard = result.get("hard_oracle", {})
    oracle_backed_pass = any(
        obligation.get("status") == "PASS"
        and obligation.get("evidence_packet", {}).get("source_kind")
        == "hard_oracle_report"
        for obligation in obligations
    )
    if oracle_backed_pass:
        replay = load_json(_repo_path(R000_REPLAY_RELATIVE))
        recorded = next((
            item for item in replay.get("accepted_results", [])
            + replay.get("mutation_results", [])
            if item.get("candidate_id") == result.get("candidate_id")
        ), None)
        if (
            recorded is None
            or recorded.get("hard_oracle", {}).get("report_sha256")
            != hard.get("report_sha256")
        ):
            errors.append(
                "PASS evidence is not bound to the frozen parent replay result"
            )
    if hard.get("hard_accepted") is not True and result.get("shadow_search_score") == 1.0:
        errors.append("hard failure cannot receive shadow score 1.0")
    expected_vector = compute_progress_vector(
        hard.get("hard_accepted") is True, obligations, parent
    )
    if result.get("shadow_progress_vector") != expected_vector:
        errors.append("shadow progress vector does not match verified obligations")
    return errors


def legacy_projection(result: dict[str, Any]) -> dict[str, Any]:
    """Normalize parent and child to the exact common byte-comparison domain."""

    return {
        "candidate_id": result["candidate_id"],
        "route": result["route"],
        "hard_oracle": result["hard_oracle"],
        "obligations": [
            {
                "criterion_id": item["criterion_id"],
                "status": item["status"],
                "evidence": item["evidence"],
                "rationale": item["rationale"],
            }
            for item in result["obligations"]
        ],
        "failure_frontier": result["failure_frontier"],
        "shadow_search_score": result["shadow_search_score"],
        "score_semantics": result["score_semantics"],
        "controls_selection": result["controls_selection"],
        "mathematical_acceptance": result["mathematical_acceptance"],
    }


def output_noise_errors(value: Any, path: str = "$") -> list[str]:
    errors: list[str] = []
    if isinstance(value, dict):
        for key, item in value.items():
            errors.extend(output_noise_errors(item, f"{path}.{key}"))
    elif isinstance(value, list):
        for index, item in enumerate(value):
            errors.extend(output_noise_errors(item, f"{path}[{index}]"))
    elif isinstance(value, str):
        if any(fragment in value for fragment in FORBIDDEN_OUTPUT_FRAGMENTS):
            errors.append(f"{path}: contains an absolute machine path")
        if TIMESTAMP_RE.search(value):
            errors.append(f"{path}: contains a timestamp")
    return errors
