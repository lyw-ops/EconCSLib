#!/usr/bin/env python3
"""Deterministically evaluate the public EvE Mathlib-style smoke candidate."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Any


SCRIPT_ROOT = Path(__file__).resolve().parent
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

from evaluator_common import (  # noqa: E402
    CommandResult,
    TRUST_BYPASS_PATTERN,
    axioms as common_axioms,
    boundary_failures as common_boundary_failures,
    load_guard_module,
    load_json,
    normalize_output,
    protected_hashes,
    run as common_run,
    safe_directory,
    sha256,
    tree_files,
    write_report,
    write_score as common_write_score,
)


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = SIDECAR_ROOT.parents[1]
CASE_PATH = SIDECAR_ROOT / "smoke" / "case.json"
DEFAULT_BASELINE = SIDECAR_ROOT / "smoke" / "seed"
EVALUATOR_TMP_ROOT = SIDECAR_ROOT / ".runtime" / "evaluator-tmp"
STATIC_GUARD = (
    REPO_ROOT / "benchmarks" / "mathlib-style" / "scripts" / "static_lean_guard.py"
)
RULES_PATH = REPO_ROOT / "benchmarks" / "mathlib-style" / "manifests" / "RULES.json"
VALIDATORS_PATH = (
    REPO_ROOT / "benchmarks" / "mathlib-style" / "manifests" / "VALIDATORS.json"
)
MANUAL_PATH = REPO_ROOT / "docs" / "research" / "mathlib-style" / "MANUAL_EN.md"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.30.0"
EXPECTED_MATHLIB_COMMIT = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
EDITABLE_FILE = "Candidate.lean"
MAX_CANDIDATE_BYTES = 64 * 1024
TIMEOUT_SECONDS = 90


def _sha256(path: Path) -> str:
    return sha256(path)


def _json(path: Path) -> dict[str, Any]:
    return load_json(path)


def _is_relative_to(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def _safe_directory(path: Path, *, label: str) -> Path:
    return safe_directory(path, label=label, repository_root=REPO_ROOT)


def _tree_files(root: Path) -> dict[str, Path]:
    return tree_files(root)


def _boundary_failures(baseline: Path, candidate: Path) -> list[str]:
    return common_boundary_failures(
        baseline, candidate, editable_file=EDITABLE_FILE
    )


def _load_guard_module() -> Any:
    return load_guard_module(
        STATIC_GUARD, module_name="econcslib_mathlib_static_guard"
    )


def _run(
    command: list[str], *, cwd: Path, timeout: int = TIMEOUT_SECONDS
) -> CommandResult:
    return common_run(command, cwd=cwd, timeout=timeout)


def _normalize_output(text: str, temporary_root: Path) -> str:
    return normalize_output(text, temporary_root, REPO_ROOT)


def _protected_hashes() -> dict[str, str]:
    paths = (
        Path(__file__).resolve(),
        SIDECAR_ROOT / "scripts" / "evaluation.sh",
        CASE_PATH,
        MANUAL_PATH,
        RULES_PATH,
        VALIDATORS_PATH,
        STATIC_GUARD,
        SCRIPT_ROOT / "evaluator_common.py",
    )
    return protected_hashes(paths)


def _validate_normative_contract(case: dict[str, Any], baseline_file: Path) -> None:
    if case.get("seed_candidate_sha256") != _sha256(baseline_file):
        raise ValueError("seed candidate hash does not match smoke/case.json")
    rules = _json(RULES_PATH).get("rules")
    if not isinstance(rules, list):
        raise ValueError("RULES.json has no rule list")
    fmt008 = next((item for item in rules if item.get("id") == "FMT-008"), None)
    if not isinstance(fmt008, dict):
        raise ValueError("FMT-008 is missing from RULES.json")
    validator_ids = fmt008.get("automation", {}).get("validator_ids", [])
    if (
        fmt008.get("rule_strength") != "MUST"
        or "linter.style.dollarSyntax" not in validator_ids
    ):
        raise ValueError("FMT-008 registry contract drifted")
    validators = _json(VALIDATORS_PATH)
    standard = validators.get("standard_set_exact_members", [])
    if "linter.style.dollarSyntax" not in standard:
        raise ValueError("dollarSyntax is not in the pinned standard linter set")


def _validate_environment() -> tuple[bool, list[str]]:
    failures: list[str] = []
    toolchain_path = REPO_ROOT / "lean-toolchain"
    if toolchain_path.read_text(encoding="utf-8").strip() != EXPECTED_TOOLCHAIN:
        failures.append("lean-toolchain-mismatch")
    mathlib = _run(
        [
            "git",
            "-C",
            str(REPO_ROOT / ".lake" / "packages" / "mathlib"),
            "rev-parse",
            "HEAD",
        ],
        cwd=REPO_ROOT,
    )
    if mathlib.returncode != 0 or mathlib.output.strip() != EXPECTED_MATHLIB_COMMIT:
        failures.append("mathlib-commit-mismatch")
    lean = _run(["lake", "env", "lean", "--version"], cwd=REPO_ROOT)
    if lean.returncode != 0 or "version 4.30.0" not in lean.output:
        failures.append("lean-version-mismatch")
    return not failures, failures


def _contract_suffix() -> str:
    return """

namespace EconCSLibEvESmokeContract

universe v

example {α : Type v} (f : α → α) (x : α) :
    EconCSLibEvESmoke.applyTwice f x = f (f x) := by
  rfl

#print axioms EconCSLibEvESmoke.applyTwice

end EconCSLibEvESmokeContract
"""


def _compile_candidate(
    source: str, temporary_root: Path
) -> tuple[CommandResult, list[str]]:
    contract_source = temporary_root / "CandidateContract.lean"
    contract_source.write_text(source.rstrip() + _contract_suffix(), encoding="utf-8")
    result = _run(
        [
            "lake",
            "env",
            "lean",
            "-D",
            "linter.mathlibStandardSet=true",
            "-o",
            str(temporary_root / "CandidateContract.olean"),
            str(contract_source),
        ],
        cwd=REPO_ROOT,
    )
    warnings = sorted(
        {
            line.strip()
            for line in result.output.splitlines()
            if "warning:" in line.lower()
        }
    )
    return result, warnings


def _run_text_linter(source: str, temporary_root: Path) -> CommandResult:
    lint_root = temporary_root / "lint-project"
    (lint_root / "EconCSLib").mkdir(parents=True)
    (lint_root / "scripts").mkdir()
    (lint_root / "EconCSLib" / "EvESmokeCandidate.lean").write_text(
        source, encoding="utf-8"
    )
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        shutil.copy2(REPO_ROOT / name, lint_root / name)
    os.symlink(REPO_ROOT / ".lake", lint_root / ".lake", target_is_directory=True)
    shutil.copy2(
        REPO_ROOT / ".lake" / "packages" / "mathlib" / "scripts" / "nolints-style.txt",
        lint_root / "scripts" / "nolints-style.txt",
    )
    return _run(
        ["lake", "exe", "lint-style", "EconCSLib.EvESmokeCandidate"],
        cwd=lint_root,
    )


def _axioms(output: str) -> list[str]:
    return common_axioms(output)


def evaluate_candidate(
    candidate_dir: Path, baseline_dir: Path = DEFAULT_BASELINE
) -> dict[str, Any]:
    """Evaluate one candidate directory and return a stable report."""
    candidate = _safe_directory(candidate_dir, label="candidate directory")
    baseline = _safe_directory(baseline_dir, label="baseline directory")
    case = _json(CASE_PATH)
    protected_before = _protected_hashes()
    gates: dict[str, bool] = {
        "boundary": False,
        "environment": False,
        "static_guard": False,
        "trusted_bypass_guard": False,
        "compile": False,
        "warning_policy": False,
        "target_issue_resolved": False,
        "statement_and_value_preserved": False,
        "axiom_delta_empty": False,
        "text_linter": False,
        "evaluator_unchanged": False,
    }
    failures: list[str] = []
    diagnostics: list[str] = []

    try:
        _validate_normative_contract(case, baseline / EDITABLE_FILE)
        boundary_failures = _boundary_failures(baseline, candidate)
        if boundary_failures:
            failures.extend(boundary_failures)
            return _finish_report(gates, failures, diagnostics, protected_before)
        gates["boundary"] = True

        environment_ok, environment_failures = _validate_environment()
        gates["environment"] = environment_ok
        failures.extend(environment_failures)
        if not environment_ok:
            return _finish_report(gates, failures, diagnostics, protected_before)

        candidate_file = candidate / EDITABLE_FILE
        if candidate_file.stat().st_size > MAX_CANDIDATE_BYTES:
            failures.append("candidate-too-large")
            return _finish_report(gates, failures, diagnostics, protected_before)
        source = candidate_file.read_text(encoding="utf-8")

        guard = _run(
            [sys.executable, str(STATIC_GUARD), str(candidate_file)], cwd=REPO_ROOT
        )
        gates["static_guard"] = guard.returncode == 0
        if not gates["static_guard"]:
            failures.append("forbidden-construct")

        clean_source = _load_guard_module().strip_comments_and_strings(source)
        gates["trusted_bypass_guard"] = (
            TRUST_BYPASS_PATTERN.search(clean_source) is None
        )
        if not gates["trusted_bypass_guard"]:
            failures.append("trusted-bypass")
        if not gates["static_guard"] or not gates["trusted_bypass_guard"]:
            return _finish_report(gates, failures, diagnostics, protected_before)

        EVALUATOR_TMP_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(
            prefix="econcslib-eve-smoke-", dir=EVALUATOR_TMP_ROOT
        ) as raw_temp:
            temporary_root = Path(raw_temp)
            compilation, warnings = _compile_candidate(source, temporary_root)
            normalized = _normalize_output(compilation.output, temporary_root)
            gates["compile"] = compilation.returncode == 0
            if not gates["compile"]:
                failures.append("compile-failed")
                if normalized:
                    diagnostics.append(normalized[:1000])
                return _finish_report(gates, failures, diagnostics, protected_before)

            gates["warning_policy"] = not warnings
            gates["target_issue_resolved"] = not any(
                "use '<|' instead of '$'" in warning for warning in warnings
            )
            if not gates["warning_policy"]:
                failures.append("unexpected-warning")
            if not gates["target_issue_resolved"]:
                failures.append("target-issue-unresolved")
            if warnings:
                diagnostics.extend(
                    _normalize_output(warning, temporary_root) for warning in warnings
                )
                return _finish_report(gates, failures, diagnostics, protected_before)

            gates["statement_and_value_preserved"] = True
            observed_axioms = _axioms(compilation.output)
            gates["axiom_delta_empty"] = not observed_axioms
            if observed_axioms:
                failures.append("axiom-delta-nonempty")

            text_linter = _run_text_linter(source, temporary_root)
            gates["text_linter"] = text_linter.returncode == 0
            if not gates["text_linter"]:
                failures.append("text-linter-failed")
                normalized_lint = _normalize_output(text_linter.output, temporary_root)
                if normalized_lint:
                    diagnostics.append(normalized_lint[:1000])
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        failures.append(f"evaluator-input-error:{type(exc).__name__}")

    return _finish_report(gates, failures, diagnostics, protected_before)


def _finish_report(
    gates: dict[str, bool],
    failures: list[str],
    diagnostics: list[str],
    protected_before: dict[str, str],
) -> dict[str, Any]:
    protected_after = _protected_hashes()
    gates["evaluator_unchanged"] = protected_before == protected_after
    if not gates["evaluator_unchanged"]:
        failures.append("protected-evaluator-asset-changed")
    passed = all(gates.values()) and not failures
    return {
        "schema_version": "1.0.0",
        "status": "passed" if passed else "failed",
        "score": 1.0 if passed else 0.0,
        "summary": (
            "all deterministic smoke gates passed"
            if passed
            else "one or more deterministic smoke gates failed"
        ),
        "gates": gates,
        "failure_codes": sorted(set(failures)),
        "diagnostics": diagnostics,
        "environment": {
            "lean_toolchain": EXPECTED_TOOLCHAIN,
            "mathlib_commit": EXPECTED_MATHLIB_COMMIT,
            "target_rule": "FMT-008",
            "validator": "linter.style.dollarSyntax",
        },
    }


def write_score(path: Path, report: dict[str, Any]) -> None:
    """Write the exact EvE 0.2.0 score PyTree used by this smoke."""
    common_write_score(path, report)


def _write_report(path: Path, report: dict[str, Any]) -> None:
    write_report(path, report)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate-dir", type=Path, required=True)
    parser.add_argument("--baseline-dir", type=Path, default=DEFAULT_BASELINE)
    parser.add_argument("--score-output", type=Path)
    parser.add_argument("--report-output", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    report = evaluate_candidate(args.candidate_dir, args.baseline_dir)
    if args.score_output is not None:
        write_score(args.score_output, report)
    if args.report_output is not None:
        _write_report(args.report_output, report)
    print(f"EvE smoke evaluation: {report['status']} (score={report['score']:.1f})")
    if report["failure_codes"]:
        print("Failure codes: " + ", ".join(report["failure_codes"]))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
