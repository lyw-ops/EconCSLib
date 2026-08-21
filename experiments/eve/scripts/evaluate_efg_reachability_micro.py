#!/usr/bin/env python3
"""Deterministically evaluate the public Stage 1a EFG usability micro-pilot."""

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
    TRUST_BYPASS_PATTERN,
    axioms,
    boundary_failures,
    load_guard_module,
    load_json,
    normalize_output,
    protected_hashes,
    run,
    safe_directory,
    sha256,
    source_imports,
    write_report,
    write_score,
)


SIDECAR_ROOT = SCRIPT_ROOT.parent
REPO_ROOT = SIDECAR_ROOT.parents[1]
TASK_ROOT = SIDECAR_ROOT / "efg_reachability_micro"
CASE_PATH = TASK_ROOT / "case.json"
DEFAULT_BASELINE = TASK_ROOT / "seed"
EVALUATOR_TMP_ROOT = SIDECAR_ROOT / ".runtime" / "evaluator-tmp"
STATIC_GUARD = (
    REPO_ROOT / "benchmarks" / "mathlib-style" / "scripts" / "static_lean_guard.py"
)
API_GROWTH_CHECK = REPO_ROOT / "scripts" / "check_efg_api_growth.py"
GOVERNANCE_CHECK = REPO_ROOT / "scripts" / "check_efg_governance.py"
API_GROWTH_BASELINE = REPO_ROOT / "scripts" / "efg_api_growth_baseline.json"
STRUCTURAL_HISTORY = (
    REPO_ROOT
    / "EconCSLib"
    / "GameTheory"
    / "ExtensiveGame"
    / "Structural"
    / "History.lean"
)
STRUCTURAL_CORE = (
    REPO_ROOT
    / "EconCSLib"
    / "GameTheory"
    / "ExtensiveGame"
    / "Interface"
    / "StructuralCore.lean"
)
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.30.0"
EXPECTED_MATHLIB_COMMIT = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
EDITABLE_FILE = "Candidate.lean"
ALLOWED_IMPORTS = [
    "EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore"
]
REQUIRED_DECLARATIONS = [
    "EconCSLibEvEEFGReachabilityMicro.reachability_history_bridge",
    "EconCSLibEvEEFGReachabilityMicro.left_reachable",
    "EconCSLibEvEEFGReachabilityMicro.right_reachable",
    "EconCSLibEvEEFGReachabilityMicro.reachability_proofs_eq",
    "EconCSLibEvEEFGReachabilityMicro.histories_ne",
    "EconCSLibEvEEFGReachabilityMicro.occurrence_endpoints_eq",
    "EconCSLibEvEEFGReachabilityMicro.occurrences_ne",
]
TASK_MARKER = "/-! ## Solver declarations -/"
MAX_CANDIDATE_BYTES = 96 * 1024
TIMEOUT_SECONDS = 90

GATE_NAMES = (
    "boundary",
    "protected_assets_initial",
    "import_allowlist",
    "task_prefix",
    "static_guard",
    "trusted_bypass_guard",
    "environment",
    "compile",
    "warning_policy",
    "target_declaration",
    "diamond_regression",
    "axiom_delta_empty",
    "efg_api_growth",
    "efg_governance",
    "protected_assets_final",
)


def _protected_paths() -> tuple[Path, ...]:
    return (
        Path(__file__).resolve(),
        SCRIPT_ROOT / "evaluator_common.py",
        SCRIPT_ROOT / "evaluation_efg_reachability_micro.sh",
        CASE_PATH,
        DEFAULT_BASELINE / "Candidate.lean",
        DEFAULT_BASELINE / "README.md",
        STATIC_GUARD,
        API_GROWTH_CHECK,
        GOVERNANCE_CHECK,
        API_GROWTH_BASELINE,
        STRUCTURAL_HISTORY,
        STRUCTURAL_CORE,
    )


def _expected_protected_failures(case: dict[str, Any]) -> list[str]:
    expected = case.get("protected_assets")
    if not isinstance(expected, dict):
        return ["protected-assets-contract-invalid"]
    failures: list[str] = []
    for relative, expected_hash in sorted(expected.items()):
        if not isinstance(relative, str) or not isinstance(expected_hash, str):
            failures.append("protected-assets-contract-invalid")
            continue
        path = (REPO_ROOT / relative).resolve()
        if not path.is_relative_to(REPO_ROOT.resolve()):
            failures.append("protected-asset-path-invalid")
        elif not path.is_file() or sha256(path) != expected_hash:
            failures.append(f"protected-asset-hash-mismatch:{relative}")
    return failures


def _case_contract_failures(case: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if case.get("allowed_imports") != ALLOWED_IMPORTS:
        failures.append("case-import-allowlist-invalid")
    if case.get("required_declarations") != REQUIRED_DECLARATIONS:
        failures.append("case-declaration-contract-invalid")
    if case.get("editable_files") != [EDITABLE_FILE]:
        failures.append("case-editable-files-invalid")
    if case.get("editable_folders") != []:
        failures.append("case-editable-folders-invalid")
    if case.get("warning_allowlist") != []:
        failures.append("case-warning-allowlist-invalid")
    score = case.get("score")
    if not isinstance(score, dict):
        failures.append("case-score-contract-invalid")
    elif (
        score.get("direction") != "higher-is-better"
        or score.get("pass") != 1.0
        or score.get("failure") != 0.0
        or score.get("boundary_failure") != 0.0
    ):
        failures.append("case-score-contract-invalid")
    return failures


def _task_prefix(source: str) -> str | None:
    if source.count(TASK_MARKER) != 1:
        return None
    before, marker, after = source.partition(TASK_MARKER)
    if not after.startswith("\n"):
        return None
    return before + marker + "\n"


def _sha256_text(value: str) -> str:
    import hashlib

    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _validate_environment() -> tuple[bool, list[str]]:
    failures: list[str] = []
    toolchain = (REPO_ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != EXPECTED_TOOLCHAIN:
        failures.append("lean-toolchain-mismatch")
    mathlib = run(
        [
            "git",
            "-C",
            str(REPO_ROOT / ".lake" / "packages" / "mathlib"),
            "rev-parse",
            "HEAD",
        ],
        cwd=REPO_ROOT,
        timeout=TIMEOUT_SECONDS,
    )
    if mathlib.returncode != 0 or mathlib.output.strip() != EXPECTED_MATHLIB_COMMIT:
        failures.append("mathlib-commit-mismatch")
    lean = run(
        ["lake", "env", "lean", "--version"],
        cwd=REPO_ROOT,
        timeout=TIMEOUT_SECONDS,
    )
    if lean.returncode != 0 or "version 4.30.0" not in lean.output:
        failures.append("lean-version-mismatch")
    return not failures, failures


def _bridge_contract() -> str:
    return """

namespace EconCSLibEvEEFGReachabilityMicroContract

open EconCSLibEvEEFGReachabilityMicro

example (A : Arena) (start finish : A.State) :
    A.Reachable start finish ↔ Nonempty (A.History start finish) :=
  reachability_history_bridge A start finish

#print axioms EconCSLibEvEEFGReachabilityMicro.reachability_history_bridge

end EconCSLibEvEEFGReachabilityMicroContract
"""


def _diamond_contract() -> str:
    return """

namespace EconCSLibEvEEFGReachabilityMicroDiamondContract

open EconCSLibEvEEFGReachabilityMicro

example : diamondArena.Reachable DiamondState.root DiamondState.merged :=
  left_reachable

example : diamondArena.Reachable DiamondState.root DiamondState.merged :=
  right_reachable

example : leftHistory.toReachable = rightHistory.toReachable :=
  reachability_proofs_eq

example : leftHistory ≠ rightHistory := histories_ne

example : leftOccurrence.1 = rightOccurrence.1 := occurrence_endpoints_eq

example : leftOccurrence ≠ rightOccurrence := occurrences_ne

#print axioms EconCSLibEvEEFGReachabilityMicro.left_reachable
#print axioms EconCSLibEvEEFGReachabilityMicro.right_reachable
#print axioms EconCSLibEvEEFGReachabilityMicro.reachability_proofs_eq
#print axioms EconCSLibEvEEFGReachabilityMicro.histories_ne
#print axioms EconCSLibEvEEFGReachabilityMicro.occurrence_endpoints_eq
#print axioms EconCSLibEvEEFGReachabilityMicro.occurrences_ne

end EconCSLibEvEEFGReachabilityMicroDiamondContract
"""


def _compile_source(
    source: str, *, name: str, temporary_root: Path
) -> tuple[Any, list[str]]:
    source_path = temporary_root / f"{name}.lean"
    source_path.write_text(source.rstrip() + "\n", encoding="utf-8")
    result = run(
        [
            "lake",
            "env",
            "lean",
            "-D",
            "linter.mathlibStandardSet=true",
            "-o",
            str(temporary_root / f"{name}.olean"),
            str(source_path),
        ],
        cwd=REPO_ROOT,
        timeout=TIMEOUT_SECONDS,
    )
    warnings = sorted(
        {
            line.strip()
            for line in result.output.splitlines()
            if "warning:" in line.lower()
        }
    )
    return result, warnings


def _finish_report(
    gates: dict[str, bool],
    failures: list[str],
    diagnostics: list[str],
    protected_before: dict[str, str],
    expected_protected_ok: bool,
) -> dict[str, Any]:
    try:
        protected_after = protected_hashes(_protected_paths())
        gates["protected_assets_final"] = (
            expected_protected_ok and protected_before == protected_after
        )
    except OSError:
        gates["protected_assets_final"] = False
    if not gates["protected_assets_final"]:
        failures.append("protected-asset-changed")
    passed = all(gates.values()) and not failures
    return {
        "schema_version": "1.0.0",
        "status": "passed" if passed else "failed",
        "score": 1.0 if passed else 0.0,
        "summary": (
            "all deterministic EFG micro-pilot gates passed"
            if passed
            else "one or more deterministic EFG micro-pilot gates failed"
        ),
        "gates": gates,
        "failure_codes": sorted(set(failures)),
        "diagnostics": diagnostics,
        "environment": {
            "lean_toolchain": EXPECTED_TOOLCHAIN,
            "mathlib_commit": EXPECTED_MATHLIB_COMMIT,
            "allowed_imports": ALLOWED_IMPORTS,
            "warning_allowlist": [],
        },
    }


def _input_failure_report(code: str) -> dict[str, Any]:
    gates = {name: False for name in GATE_NAMES}
    return {
        "schema_version": "1.0.0",
        "status": "failed",
        "score": 0.0,
        "summary": "one or more deterministic EFG micro-pilot gates failed",
        "gates": gates,
        "failure_codes": [code],
        "diagnostics": [],
        "environment": {
            "lean_toolchain": EXPECTED_TOOLCHAIN,
            "mathlib_commit": EXPECTED_MATHLIB_COMMIT,
            "allowed_imports": ALLOWED_IMPORTS,
            "warning_allowlist": [],
        },
    }


def evaluate_candidate(
    candidate_dir: Path, baseline_dir: Path = DEFAULT_BASELINE
) -> dict[str, Any]:
    """Evaluate one candidate directory and return a stable fail-closed report."""

    gates = {name: False for name in GATE_NAMES}
    failures: list[str] = []
    diagnostics: list[str] = []
    protected_before: dict[str, str] = {}
    expected_protected_ok = False

    try:
        candidate = safe_directory(
            candidate_dir, label="candidate directory", repository_root=REPO_ROOT
        )
        baseline = safe_directory(
            baseline_dir, label="baseline directory", repository_root=REPO_ROOT
        )
        case = load_json(CASE_PATH)
        protected_before = protected_hashes(_protected_paths())

        protected_failures = _expected_protected_failures(case)
        expected_protected_ok = not protected_failures
        failures.extend(protected_failures)
        if protected_failures:
            return _finish_report(
                gates,
                failures,
                diagnostics,
                protected_before,
                expected_protected_ok,
            )
        gates["protected_assets_initial"] = True

        case_failures = _case_contract_failures(case)
        failures.extend(case_failures)
        if case_failures:
            return _finish_report(
                gates,
                failures,
                diagnostics,
                protected_before,
                expected_protected_ok,
            )

        failures.extend(
            boundary_failures(baseline, candidate, editable_file=EDITABLE_FILE)
        )
        if failures:
            return _finish_report(
                gates,
                failures,
                diagnostics,
                protected_before,
                expected_protected_ok,
            )
        gates["boundary"] = True

        baseline_candidate = baseline / EDITABLE_FILE
        if case.get("seed_candidate_sha256") != sha256(baseline_candidate):
            failures.append("seed-candidate-hash-mismatch")
            return _finish_report(
                gates,
                failures,
                diagnostics,
                protected_before,
                expected_protected_ok,
            )

        candidate_file = candidate / EDITABLE_FILE
        if candidate_file.stat().st_size > MAX_CANDIDATE_BYTES:
            failures.append("candidate-too-large")
            return _finish_report(
                gates,
                failures,
                diagnostics,
                protected_before,
                expected_protected_ok,
            )
        source = candidate_file.read_text(encoding="utf-8")
        guard_module = load_guard_module(
            STATIC_GUARD, module_name="econcslib_efg_micro_static_guard"
        )
        clean_source = guard_module.strip_comments_and_strings(source)

        imports = source_imports(clean_source)
        gates["import_allowlist"] = imports == ALLOWED_IMPORTS
        if not gates["import_allowlist"]:
            failures.append("forbidden-import")
            return _finish_report(
                gates,
                failures,
                diagnostics,
                protected_before,
                expected_protected_ok,
            )

        prefix = _task_prefix(source)
        gates["task_prefix"] = (
            prefix is not None
            and _sha256_text(prefix) == case.get("protected_prefix_sha256")
        )
        if not gates["task_prefix"]:
            failures.append("protected-task-prefix-changed")
            return _finish_report(
                gates,
                failures,
                diagnostics,
                protected_before,
                expected_protected_ok,
            )

        guard = run(
            [sys.executable, str(STATIC_GUARD), str(candidate_file)],
            cwd=REPO_ROOT,
            timeout=TIMEOUT_SECONDS,
        )
        gates["static_guard"] = guard.returncode == 0
        if not gates["static_guard"]:
            failures.append("forbidden-construct")

        gates["trusted_bypass_guard"] = (
            TRUST_BYPASS_PATTERN.search(clean_source) is None
        )
        if not gates["trusted_bypass_guard"]:
            failures.append("trusted-bypass")
        if not gates["static_guard"] or not gates["trusted_bypass_guard"]:
            return _finish_report(
                gates,
                failures,
                diagnostics,
                protected_before,
                expected_protected_ok,
            )

        environment_ok, environment_failures = _validate_environment()
        gates["environment"] = environment_ok
        failures.extend(environment_failures)
        if not environment_ok:
            return _finish_report(
                gates,
                failures,
                diagnostics,
                protected_before,
                expected_protected_ok,
            )

        EVALUATOR_TMP_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(
            prefix="econcslib-eve-efg-micro-", dir=EVALUATOR_TMP_ROOT
        ) as raw_temp:
            temporary_root = Path(raw_temp)
            candidate_compile, candidate_warnings = _compile_source(
                source, name="Candidate", temporary_root=temporary_root
            )
            gates["compile"] = candidate_compile.returncode == 0
            if not gates["compile"]:
                failures.append("compile-failed")
                output = normalize_output(
                    candidate_compile.output, temporary_root, REPO_ROOT
                )
                if output:
                    diagnostics.append(output[:1200])
                return _finish_report(
                    gates,
                    failures,
                    diagnostics,
                    protected_before,
                    expected_protected_ok,
                )

            bridge_compile, bridge_warnings = _compile_source(
                source.rstrip() + _bridge_contract(),
                name="BridgeContract",
                temporary_root=temporary_root,
            )
            gates["target_declaration"] = bridge_compile.returncode == 0
            if not gates["target_declaration"]:
                failures.append("target-declaration-missing-or-wrong-type")
                output = normalize_output(
                    bridge_compile.output, temporary_root, REPO_ROOT
                )
                if output:
                    diagnostics.append(output[:1200])
                return _finish_report(
                    gates,
                    failures,
                    diagnostics,
                    protected_before,
                    expected_protected_ok,
                )

            diamond_compile, diamond_warnings = _compile_source(
                source.rstrip() + _diamond_contract(),
                name="DiamondContract",
                temporary_root=temporary_root,
            )
            gates["diamond_regression"] = diamond_compile.returncode == 0
            if not gates["diamond_regression"]:
                failures.append("diamond-regression-missing-or-invalid")
                output = normalize_output(
                    diamond_compile.output, temporary_root, REPO_ROOT
                )
                if output:
                    diagnostics.append(output[:1200])
                return _finish_report(
                    gates,
                    failures,
                    diagnostics,
                    protected_before,
                    expected_protected_ok,
                )

            warnings = sorted(
                set(candidate_warnings + bridge_warnings + diamond_warnings)
            )
            gates["warning_policy"] = not warnings
            if warnings:
                failures.append("unexpected-warning")
                diagnostics.extend(warnings)
                return _finish_report(
                    gates,
                    failures,
                    diagnostics,
                    protected_before,
                    expected_protected_ok,
                )

            target_axioms = sorted(
                set(axioms(bridge_compile.output) + axioms(diamond_compile.output))
            )
            gates["axiom_delta_empty"] = not target_axioms
            if target_axioms:
                failures.append("target-axiom-delta-nonempty")
                diagnostics.append("target axioms: " + ", ".join(target_axioms))
                return _finish_report(
                    gates,
                    failures,
                    diagnostics,
                    protected_before,
                    expected_protected_ok,
                )

        if protected_hashes(_protected_paths()) != protected_before:
            failures.append("protected-asset-changed-after-lean")
            return _finish_report(
                gates,
                failures,
                diagnostics,
                protected_before,
                expected_protected_ok,
            )

        api_growth = run(
            [sys.executable, str(API_GROWTH_CHECK)],
            cwd=REPO_ROOT,
            timeout=TIMEOUT_SECONDS,
        )
        gates["efg_api_growth"] = api_growth.returncode == 0
        if not gates["efg_api_growth"]:
            failures.append("efg-api-growth-regression")
            diagnostics.append(api_growth.output[:1200])
            return _finish_report(
                gates,
                failures,
                diagnostics,
                protected_before,
                expected_protected_ok,
            )

        governance = run(
            [sys.executable, str(GOVERNANCE_CHECK)],
            cwd=REPO_ROOT,
            timeout=TIMEOUT_SECONDS,
        )
        gates["efg_governance"] = governance.returncode == 0
        if not gates["efg_governance"]:
            failures.append("efg-governance-regression")
            diagnostics.append(governance.output[:1200])
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        failures.append(f"evaluator-input-error:{type(exc).__name__}")

    return _finish_report(
        gates,
        failures,
        diagnostics,
        protected_before,
        expected_protected_ok,
    )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate-dir", type=Path, required=True)
    parser.add_argument("--baseline-dir", type=Path, default=DEFAULT_BASELINE)
    parser.add_argument("--score-output", type=Path)
    parser.add_argument("--report-output", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        report = evaluate_candidate(args.candidate_dir, args.baseline_dir)
    except Exception as exc:  # fail closed and still emit the worst score
        report = _input_failure_report(f"evaluator-failed:{type(exc).__name__}")
    if args.score_output is not None:
        write_score(args.score_output, report)
    if args.report_output is not None:
        write_report(args.report_output, report)
    print(
        "EvE EFG micro-pilot evaluation: "
        f"{report['status']} (score={report['score']:.1f})"
    )
    if report["failure_codes"]:
        print("Failure codes: " + ", ".join(report["failure_codes"]))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
