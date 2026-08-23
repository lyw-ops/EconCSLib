#!/usr/bin/env python3
"""Deterministic helpers for the R000 shadow-only rubric instrumentation."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
import tempfile
from pathlib import Path
from typing import Any


SCRIPT_ROOT = Path(__file__).resolve().parent
RUBRIC_ROOT = SCRIPT_ROOT.parent
SIDECAR_ROOT = RUBRIC_ROOT.parent
REPO_ROOT = SIDECAR_ROOT.parents[1]
R000_PATH = RUBRIC_ROOT / "versions" / "R000.json"
LEGACY_EVALUATOR_PATH = SIDECAR_ROOT / "scripts" / "evaluate_stage2_entry_game.py"

STATUSES = {"PASS", "FAIL", "NOT_EVALUATED", "NOT_APPLICABLE", "UNKNOWN"}

# This is the evaluator's execution order, not the presentation order of its
# GATE_NAMES tuple. The final protected-assets check is special: _report runs it
# on every return path.
CORE_STAGE = {
    "CORE.PROTECTED_ASSETS_INITIAL": 0,
    "CORE.EDIT_BOUNDARY": 1,
    "CORE.SOURCE_LOCK": 2,
    "CORE.IMPORT_BOUNDARY": 3,
    "CORE.TASK_IDENTITY": 4,
    "CORE.NO_PLACEHOLDER": 5,
    "CORE.NO_TRUSTED_BYPASS": 5,
    "CORE.ROUTE_IDENTITY": 6,
    "CORE.ENVIRONMENT": 7,
    "CORE.COMPILATION": 8,
    "CORE.TARGET_DECLARATIONS": 9,
    "CORE.WARNING_POLICY": 10,
    "CORE.AXIOM_ALLOWLIST": 11,
    "CORE.PROTECTED_ASSETS_FINAL": 12,
}

CRITERION_GATE = {
    "CORE.PROTECTED_ASSETS_INITIAL": "protected_assets_initial",
    "CORE.EDIT_BOUNDARY": "boundary",
    "CORE.IMPORT_BOUNDARY": "import_allowlist",
    "CORE.TASK_IDENTITY": "task_prefix",
    "CORE.NO_PLACEHOLDER": "static_guard",
    "CORE.NO_TRUSTED_BYPASS": "trusted_bypass_guard",
    "CORE.ROUTE_IDENTITY": "route_discipline",
    "CORE.ENVIRONMENT": "environment",
    "CORE.COMPILATION": "compile",
    "CORE.TARGET_DECLARATIONS": "target_declarations",
    "CORE.WARNING_POLICY": "warning_policy",
    "CORE.AXIOM_ALLOWLIST": "axiom_allowlist",
    "CORE.PROTECTED_ASSETS_FINAL": "protected_assets_final",
}

# Prefixes ending in ':' intentionally match parameterized legacy codes.
FAILURE_RULES: tuple[tuple[str, str], ...] = (
    ("protected-assets-contract-invalid", "CORE.PROTECTED_ASSETS_INITIAL"),
    ("protected-asset-path-invalid", "CORE.PROTECTED_ASSETS_INITIAL"),
    ("protected-asset-hash-mismatch:", "CORE.PROTECTED_ASSETS_INITIAL"),
    ("case-", "CORE.SOURCE_LOCK"),
    ("editable-file-missing", "CORE.EDIT_BOUNDARY"),
    ("forbidden-created:", "CORE.EDIT_BOUNDARY"),
    ("forbidden-deleted:", "CORE.EDIT_BOUNDARY"),
    ("forbidden-modified:", "CORE.EDIT_BOUNDARY"),
    ("seed-candidate-hash-mismatch", "CORE.SOURCE_LOCK"),
    ("candidate-too-large", "CORE.EDIT_BOUNDARY"),
    ("forbidden-import", "CORE.IMPORT_BOUNDARY"),
    ("protected-task-prefix-changed", "CORE.TASK_IDENTITY"),
    ("forbidden-construct", "CORE.NO_PLACEHOLDER"),
    ("trusted-bypass", "CORE.NO_TRUSTED_BYPASS"),
    ("route-discipline-violation", "CORE.ROUTE_IDENTITY"),
    ("lean-toolchain-mismatch", "CORE.ENVIRONMENT"),
    ("mathlib-commit-mismatch", "CORE.ENVIRONMENT"),
    ("lean-version-mismatch", "CORE.ENVIRONMENT"),
    ("compile-failed", "CORE.COMPILATION"),
    ("target-declaration-missing-or-wrong-type", "CORE.TARGET_DECLARATIONS"),
    ("unexpected-warning", "CORE.WARNING_POLICY"),
    ("target-axiom-outside-allowlist", "CORE.AXIOM_ALLOWLIST"),
    ("protected-asset-changed", "CORE.PROTECTED_ASSETS_FINAL"),
)

FRONTIER_CRITERIA = tuple(
    criterion
    for criterion, _stage in sorted(CORE_STAGE.items(), key=lambda item: (item[1], item[0]))
)
FATAL_CRITERIA = {
    "CORE.SOURCE_LOCK",
    "CORE.EDIT_BOUNDARY",
    "CORE.PROTECTED_ASSETS_INITIAL",
    "CORE.PROTECTED_ASSETS_FINAL",
    "CORE.TASK_IDENTITY",
    "CORE.NO_PLACEHOLDER",
    "CORE.NO_TRUSTED_BYPASS",
    "CORE.ROUTE_IDENTITY",
}


def canonical_json_bytes(value: Any) -> bytes:
    """Return the repository's canonical deterministic JSON encoding."""

    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(65536):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def repo_relative(path: Path) -> str:
    return path.resolve().relative_to(REPO_ROOT.resolve()).as_posix()


def _matches(code: str, pattern: str) -> bool:
    if pattern.endswith(":") or pattern == "case-":
        return code.startswith(pattern)
    return code == pattern


def failure_criteria(failure_codes: list[str]) -> dict[str, list[str]]:
    """Map known legacy failure codes to the criterion that actually failed."""

    mapped: dict[str, list[str]] = {}
    for code in failure_codes:
        for pattern, criterion_id in FAILURE_RULES:
            if _matches(code, pattern):
                mapped.setdefault(criterion_id, []).append(code)
                break
    return mapped


def _failure_stop_stage(code: str, criterion_id: str) -> int:
    """Return the actual legacy return point for one mapped failure code."""

    # Case-contract checks and boundary_failures execute in the same group.
    if code.startswith("case-"):
        return 1
    # Candidate size is checked after the seed/source identity check even
    # though it is classified as an edit-boundary failure.
    if code == "candidate-too-large":
        return 2
    return CORE_STAGE[criterion_id]


def _result(criterion_id: str, status: str, evidence: list[str], rationale: str) -> dict[str, Any]:
    if status not in STATUSES:
        raise ValueError(f"unknown obligation status: {status}")
    return {
        "criterion_id": criterion_id,
        "status": status,
        "evidence": evidence,
        "rationale": rationale,
    }


def map_core_obligations(report: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Interpret fail-fast legacy gates without treating every false as FAIL."""

    failure_codes = [str(code) for code in report.get("failure_codes", [])]
    mapped = failure_criteria(failure_codes)
    recognized = {code for codes in mapped.values() for code in codes}
    unexplained = [code for code in failure_codes if code not in recognized]
    gates = report.get("gates") if isinstance(report.get("gates"), dict) else {}

    primary_failed = [
        criterion for criterion in mapped
        if criterion != "CORE.PROTECTED_ASSETS_FINAL"
    ]
    stop_stage = min((
        _failure_stop_stage(code, criterion)
        for criterion in primary_failed
        for code in mapped[criterion]
    ), default=None)
    results: dict[str, dict[str, Any]] = {}

    for criterion_id, stage in CORE_STAGE.items():
        gate = CRITERION_GATE.get(criterion_id)
        codes = mapped.get(criterion_id, [])
        gate_evidence = [f"hard-oracle:gates.{gate}"] if gate else []
        code_evidence = [f"hard-oracle:failure-code:{code}" for code in sorted(codes)]

        if unexplained:
            results[criterion_id] = _result(
                criterion_id,
                "UNKNOWN",
                [f"hard-oracle:unmapped-failure-code:{code}" for code in sorted(unexplained)],
                "The legacy report contains an unmapped failure code, so execution cannot be inferred safely.",
            )
            continue

        if criterion_id == "CORE.PROTECTED_ASSETS_FINAL":
            if codes or gates.get(gate) is False:
                status = "FAIL"
                rationale = "The evaluator's always-run final protected-assets check failed."
            elif gates.get(gate) is True:
                status = "PASS"
                rationale = "The evaluator's always-run final protected-assets check passed."
            else:
                status = "UNKNOWN"
                rationale = "The final protected-assets result is absent or malformed."
            results[criterion_id] = _result(
                criterion_id, status, gate_evidence + code_evidence, rationale
            )
            continue

        if codes:
            results[criterion_id] = _result(
                criterion_id,
                "FAIL",
                gate_evidence + code_evidence,
                "A legacy failure code identifies this as the executed blocking frontier.",
            )
        elif stop_stage is not None and stage > stop_stage:
            results[criterion_id] = _result(
                criterion_id,
                "NOT_EVALUATED",
                [],
                "The fail-fast evaluator returned at an earlier obligation frontier.",
            )
        elif stop_stage is None or stage <= stop_stage:
            if criterion_id == "CORE.SOURCE_LOCK":
                status = "PASS"
            elif gate is not None and gates.get(gate) is True:
                status = "PASS"
            elif stage == stop_stage and stage == 5:
                # static_guard and trusted_bypass_guard execute as one group.
                status = "PASS" if gates.get(gate) is True else "UNKNOWN"
            elif stop_stage is not None and stage <= stop_stage:
                # Aggregated legacy gates can remain false even when their own
                # check passed (notably the boundary/case-contract group).
                status = "PASS"
            else:
                status = "UNKNOWN"
            rationale = (
                "The legacy evaluator executed this obligation without a mapped failure."
                if status == "PASS"
                else "The legacy report does not contain enough evidence to assign PASS or FAIL."
            )
            results[criterion_id] = _result(
                criterion_id, status, gate_evidence, rationale
            )
    return results


def _derived_route_status(
    criterion_id: str,
    prerequisite: dict[str, Any],
    *,
    pass_evidence: str,
    conservative_on_failure: bool = False,
) -> dict[str, Any]:
    status = prerequisite["status"]
    if status == "PASS":
        return _result(
            criterion_id,
            "PASS",
            [pass_evidence],
            "The compiled deterministic contract directly checks this obligation.",
        )
    if status == "FAIL" and conservative_on_failure:
        return _result(
            criterion_id,
            "UNKNOWN",
            prerequisite["evidence"],
            "The aggregate contract failed but does not identify which semantic sub-obligation failed.",
        )
    if status == "FAIL":
        return _result(
            criterion_id,
            "FAIL",
            prerequisite["evidence"],
            "The executed deterministic prerequisite for this obligation failed.",
        )
    return _result(
        criterion_id,
        "NOT_EVALUATED" if status == "NOT_EVALUATED" else "UNKNOWN",
        [],
        "The required deterministic prerequisite was not established.",
    )


def map_obligations(report: dict[str, Any], rubric: dict[str, Any], route: str) -> list[dict[str, Any]]:
    core = map_core_obligations(report)
    results: dict[str, dict[str, Any]] = dict(core)
    route_gate = core["CORE.ROUTE_IDENTITY"]
    target_gate = core["CORE.TARGET_DECLARATIONS"]

    direct_structural = {
        "DIRECT.CONCRETE_ROUTE",
        "DIRECT.NO_TRANSPORT_ABSTRACTION_LEAK",
    }
    direct_semantic = {
        "DIRECT.NASH_CHARACTERIZATION",
        "DIRECT.SPE_CHARACTERIZATION",
        "DIRECT.OFF_PATH_SEPARATION",
    }
    transport_contract = {
        "TRANSPORT.PAYOFF_PRESERVATION",
        "TRANSPORT.HYPOTHESIS_BRIDGE",
        "TRANSPORT.NASH_PRESERVATION",
        "TRANSPORT.SPE_PRESERVATION",
        "TRANSPORT.CERTIFICATE_COMPLETE",
        "TRANSPORT.CONCLUSION_TRANSPORT",
    }
    transport_syntactic = {
        "TRANSPORT.ACTION_ENCODERS",
        "TRANSPORT.PROFILE_ENCODER",
        "TRANSPORT.CERTIFICATE_CONSUMED",
        "TRANSPORT.GENERAL_NASH_THEOREM_APPLICATION",
        "TRANSPORT.GENERAL_SPE_THEOREM_APPLICATION",
        "TRANSPORT.EQUALITY_REFLECTION",
    }

    for criterion in rubric["criteria"]:
        criterion_id = criterion["criterion_id"]
        if criterion_id in results:
            continue
        applies = criterion["applies_when"]
        if applies != route:
            results[criterion_id] = _result(
                criterion_id,
                "NOT_APPLICABLE",
                [],
                f"This criterion applies only to {applies} evaluation.",
            )
        elif criterion_id in direct_structural:
            results[criterion_id] = _derived_route_status(
                criterion_id,
                route_gate,
                pass_evidence="hard-oracle:gates.route_discipline",
            )
        elif criterion_id in direct_semantic or criterion_id in transport_contract:
            results[criterion_id] = _derived_route_status(
                criterion_id,
                target_gate,
                pass_evidence="hard-oracle:gates.target_declarations:lean-kernel-contract",
                conservative_on_failure=True,
            )
        elif criterion_id in transport_syntactic:
            status = route_gate["status"]
            results[criterion_id] = _result(
                criterion_id,
                "NOT_EVALUATED" if status == "NOT_EVALUATED" else "UNKNOWN",
                ["hard-oracle:gates.route_discipline:syntactic-only"] if status == "PASS" else [],
                "Token/structure checks cannot by themselves prove this semantic transport obligation.",
            )
        else:
            results[criterion_id] = _result(
                criterion_id,
                "UNKNOWN",
                [],
                "No deterministic R000 adapter evidence is defined for this criterion.",
            )
    return [results[item["criterion_id"]] for item in rubric["criteria"]]


def compute_shadow_score(hard_accepted: bool, obligations: list[dict[str, Any]]) -> float:
    """Compute the documented monotone frontier score with integer arithmetic."""

    by_id = {item["criterion_id"]: item for item in obligations}
    if hard_accepted:
        return 1.0
    if any(by_id[item]["status"] == "FAIL" for item in FATAL_CRITERIA):
        return 0.0
    statuses = [by_id[item]["status"] for item in FRONTIER_CRITERIA]
    contiguous = 0
    for status in statuses:
        if status != "PASS":
            break
        contiguous += 1
    passed = sum(status == "PASS" for status in statuses)
    count = len(statuses)
    micro_score = 50_000 + (800_000 * contiguous // count) + (100_000 * passed // count)
    return min(0.95, micro_score / 1_000_000)


def _load_legacy_evaluator() -> Any:
    module_name = "eve_rubric_r000_legacy_stage2_evaluator"
    spec = importlib.util.spec_from_file_location(module_name, LEGACY_EVALUATOR_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load the legacy Stage 2 evaluator")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def run_hard_oracle(route: str, candidate_dir: Path) -> tuple[dict[str, Any], str]:
    """Call the old evaluator read-only while redirecting its temp parent."""

    evaluator = _load_legacy_evaluator()
    # Lean requires elaborated input files to remain below the Lake project
    # root. This disposable directory is therefore inside the new rubric
    # namespace, never under the historical experiments/eve/.runtime tree.
    with tempfile.TemporaryDirectory(
        prefix=".r000-hard-oracle-", dir=RUBRIC_ROOT
    ) as raw_temp:
        shadow_sidecar = Path(raw_temp) / "sidecar"
        shadow_sidecar.mkdir()
        evaluator.SIDECAR_ROOT = shadow_sidecar
        report = evaluator.evaluate_candidate(route, candidate_dir)
        report_bytes = canonical_json_bytes(report)
    return report, sha256_bytes(report_bytes)


def evaluate_shadow(
    route: str,
    candidate_dir: Path,
    candidate_id: str,
    rubric_path: Path = R000_PATH,
) -> dict[str, Any]:
    """Evaluate one candidate without changing the hard acceptance oracle."""

    rubric = load_json(rubric_path)
    try:
        report, report_hash = run_hard_oracle(route, candidate_dir)
        hard_accepted = (
            report.get("status") == "passed"
            and report.get("score") == 1.0
            and isinstance(report.get("gates"), dict)
            and all(report["gates"].values())
            and not report.get("failure_codes")
        )
        obligations = map_obligations(report, rubric, route)
        mapped = failure_criteria([str(code) for code in report.get("failure_codes", [])])
        primary = [item for item in mapped if item != "CORE.PROTECTED_ASSETS_FINAL"]
        if primary:
            first_stage = min(CORE_STAGE[item] for item in primary)
            frontier = sorted(item for item in primary if CORE_STAGE[item] == first_stage)
        elif "CORE.PROTECTED_ASSETS_FINAL" in mapped:
            frontier = ["CORE.PROTECTED_ASSETS_FINAL"]
        else:
            frontier = []
        shadow_score = compute_shadow_score(hard_accepted, obligations)
        hard_status = str(report.get("status", "failed"))
        hard_score = float(report.get("score", 0.0))
        failure_codes = [str(code) for code in report.get("failure_codes", [])]
    except Exception as exc:  # fail closed at the additive wrapper boundary
        error_report = {
            "schema_version": "1.0.0",
            "status": "error",
            "score": 0.0,
            "failure_codes": [f"hard-oracle-wrapper-error:{type(exc).__name__}"],
        }
        report_hash = sha256_bytes(canonical_json_bytes(error_report))
        hard_accepted = False
        hard_status = "error"
        hard_score = 0.0
        failure_codes = error_report["failure_codes"]
        frontier = ["CORE.SOURCE_LOCK"]
        obligations = []
        for criterion in rubric["criteria"]:
            status = "NOT_APPLICABLE" if criterion["applies_when"] not in ("all", route) else "UNKNOWN"
            obligations.append(_result(
                criterion["criterion_id"], status, [],
                "The shadow wrapper failed closed before reliable obligation evidence was available.",
            ))
        shadow_score = 0.0

    return {
        "schema_version": "1.0.0",
        "rubric_id": rubric["rubric_id"],
        "candidate_id": candidate_id,
        "route": route,
        "hard_oracle": {
            "adapter_path": repo_relative(LEGACY_EVALUATOR_PATH),
            "status": hard_status,
            "score": hard_score,
            "hard_accepted": hard_accepted,
            "failure_codes": failure_codes,
            "report_sha256": report_hash,
        },
        "obligations": obligations,
        "failure_frontier": frontier,
        "shadow_search_score": shadow_score,
        "score_semantics": "non-authoritative-shadow-only",
        "controls_selection": False,
        "mathematical_acceptance": False,
        "limitations": [
            "The existing deterministic binary evaluator remains the only acceptance oracle.",
            "R000 is a public Stage 2 development-corpus baseline, not benchmark or generalization evidence.",
            "Syntactic evidence is never promoted to proof of a semantic obligation.",
        ],
    }


def validate_instance(instance: Any, schema: dict[str, Any], path: str = "$") -> list[str]:
    """Validate the small JSON-Schema subset used by the checked-in schemas."""

    errors: list[str] = []
    expected_type = schema.get("type")
    if expected_type is not None:
        choices = expected_type if isinstance(expected_type, list) else [expected_type]
        predicates = {
            "object": lambda value: isinstance(value, dict),
            "array": lambda value: isinstance(value, list),
            "string": lambda value: isinstance(value, str),
            "number": lambda value: isinstance(value, (int, float)) and not isinstance(value, bool),
            "integer": lambda value: isinstance(value, int) and not isinstance(value, bool),
            "boolean": lambda value: isinstance(value, bool),
            "null": lambda value: value is None,
        }
        if not any(predicates[item](instance) for item in choices):
            return [f"{path}: expected type {expected_type}"]
    if "const" in schema and instance != schema["const"]:
        errors.append(f"{path}: expected constant {schema['const']!r}")
    if "enum" in schema and instance not in schema["enum"]:
        errors.append(f"{path}: value is not in enum")
    if isinstance(instance, dict):
        for name in schema.get("required", []):
            if name not in instance:
                errors.append(f"{path}: missing required property {name}")
        properties = schema.get("properties", {})
        for name, value in instance.items():
            if name in properties:
                errors.extend(validate_instance(value, properties[name], f"{path}.{name}"))
            elif schema.get("additionalProperties") is False:
                errors.append(f"{path}: unexpected property {name}")
    if isinstance(instance, list):
        if len(instance) < schema.get("minItems", 0):
            errors.append(f"{path}: too few items")
        if schema.get("uniqueItems"):
            serialized = [json.dumps(item, sort_keys=True) for item in instance]
            if len(serialized) != len(set(serialized)):
                errors.append(f"{path}: items are not unique")
        item_schema = schema.get("items")
        if isinstance(item_schema, dict):
            for index, value in enumerate(instance):
                errors.extend(validate_instance(value, item_schema, f"{path}[{index}]"))
    if isinstance(instance, str):
        if len(instance) < schema.get("minLength", 0):
            errors.append(f"{path}: string is too short")
    if isinstance(instance, (int, float)) and not isinstance(instance, bool):
        if "minimum" in schema and instance < schema["minimum"]:
            errors.append(f"{path}: below minimum")
        if "maximum" in schema and instance > schema["maximum"]:
            errors.append(f"{path}: above maximum")
    return errors
