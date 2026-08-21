#!/usr/bin/env python3
"""Deterministically evaluate one Stage 2 Entry Game proof route."""

from __future__ import annotations

import argparse
import json
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
TASK_ROOT = SIDECAR_ROOT / "stage2_entry_game"
STATIC_GUARD = (
    REPO_ROOT / "benchmarks" / "mathlib-style" / "scripts" / "static_lean_guard.py"
)
DISCRETE_INTERFACE = (
    REPO_ROOT
    / "EconCSLib"
    / "GameTheory"
    / "ExtensiveGame"
    / "Interface"
    / "Compilation"
    / "Discrete.lean"
)
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.30.0"
EXPECTED_MATHLIB_COMMIT = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
EDITABLE_FILE = "Candidate.lean"
ALLOWED_IMPORTS = [
    "EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete",
    "Mathlib.Tactic",
]
ALLOWED_AXIOMS = ["Classical.choice", "Quot.sound", "propext"]
MAX_CANDIDATE_BYTES = 128 * 1024
TIMEOUT_SECONDS = 120
GATE_NAMES = (
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
)


ROUTES: dict[str, dict[str, Any]] = {
    "direct": {
        "namespace": "EconCSLibEVEEntryGameDirect",
        "marker": "/-! ## Solver declarations: direct route -/",
        "required_source_tokens": (
            "direct_nash_iff",
            "direct_subgamePerfect_iff",
            "direct_out_fight_separation",
        ),
        "forbidden_source_tokens": (
            "AbstractTwoStage",
            "RefinementCertificate",
            "transport_subgamePerfect_iff",
        ),
        "required_declarations": (
            "EconCSLibEVEEntryGameDirect.direct_nash_iff",
            "EconCSLibEVEEntryGameDirect.direct_subgamePerfect_iff",
            "EconCSLibEVEEntryGameDirect.direct_out_fight_separation",
        ),
    },
    "transport": {
        "namespace": "EconCSLibEVEEntryGameTransport",
        "marker": "/-! ## Solver declarations: transport route -/",
        "required_source_tokens": (
            "entryCertificate",
            "AbstractTwoStage.nash_iff_of_strict",
            "AbstractTwoStage.unique_spe_of_strict",
            "entryCertificate.subgamePerfect_preserved",
            "entryCertificate.nash_preserved",
            "transport_subgamePerfect_iff",
            "transport_out_fight_separation",
        ),
        "forbidden_source_tokens": (),
        "required_declarations": (
            "EconCSLibEVEEntryGameTransport.encodeChallenger",
            "EconCSLibEVEEntryGameTransport.encodeIncumbent",
            "EconCSLibEVEEntryGameTransport.encodeProfile",
            "EconCSLibEVEEntryGameTransport.entryUtilities",
            "EconCSLibEVEEntryGameTransport.payoff_preserved",
            "EconCSLibEVEEntryGameTransport.hypothesis_bridge",
            "EconCSLibEVEEntryGameTransport.nash_preserved",
            "EconCSLibEVEEntryGameTransport.subgamePerfect_preserved",
            "EconCSLibEVEEntryGameTransport.entryCertificate",
            "EconCSLibEVEEntryGameTransport.abstract_nash_for_entry",
            "EconCSLibEVEEntryGameTransport.abstract_unique_spe_for_entry",
            "EconCSLibEVEEntryGameTransport.transport_subgamePerfect_iff",
            "EconCSLibEVEEntryGameTransport.transport_out_fight_separation",
        ),
    },
}


def _route_root(route: str) -> Path:
    return TASK_ROOT / route


def _case_path(route: str) -> Path:
    return _route_root(route) / "case.json"


def _default_baseline(route: str) -> Path:
    return _route_root(route) / "seed"


def _protected_paths(route: str) -> tuple[Path, ...]:
    root = _route_root(route)
    return (
        Path(__file__).resolve(),
        SCRIPT_ROOT / "evaluator_common.py",
        SCRIPT_ROOT / f"evaluation_stage2_entry_{route}.sh",
        _case_path(route),
        root / "seed" / "Candidate.lean",
        root / "seed" / "README.md",
        TASK_ROOT / "source-lock.json",
        TASK_ROOT / "TASK_SPEC.md",
        STATIC_GUARD,
        DISCRETE_INTERFACE,
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


def _case_contract_failures(case: dict[str, Any], route: str) -> list[str]:
    failures: list[str] = []
    if case.get("route") != route:
        failures.append("case-route-invalid")
    if case.get("allowed_imports") != ALLOWED_IMPORTS:
        failures.append("case-import-allowlist-invalid")
    if case.get("editable_files") != [EDITABLE_FILE]:
        failures.append("case-editable-files-invalid")
    if case.get("editable_folders") != []:
        failures.append("case-editable-folders-invalid")
    if case.get("required_declarations") != list(ROUTES[route]["required_declarations"]):
        failures.append("case-declaration-contract-invalid")
    if case.get("warning_allowlist") != []:
        failures.append("case-warning-allowlist-invalid")
    if case.get("axiom_allowlist") != ALLOWED_AXIOMS:
        failures.append("case-axiom-allowlist-invalid")
    score = case.get("score")
    if not isinstance(score, dict) or score != {
        "direction": "higher-is-better",
        "pass": 1.0,
        "failure": 0.0,
        "boundary_failure": 0.0,
    }:
        failures.append("case-score-contract-invalid")
    return failures


def _task_prefix(source: str, marker: str) -> str | None:
    if source.count(marker) != 1:
        return None
    before, found, after = source.partition(marker)
    if not after.startswith("\n"):
        return None
    return before + found + "\n"


def _sha256_text(value: str) -> str:
    import hashlib

    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _validate_environment() -> tuple[bool, list[str]]:
    failures: list[str] = []
    toolchain = (REPO_ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != EXPECTED_TOOLCHAIN:
        failures.append("lean-toolchain-mismatch")
    mathlib = run(
        ["git", "-C", str(REPO_ROOT / ".lake" / "packages" / "mathlib"),
         "rev-parse", "HEAD"],
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


def _contract(route: str) -> str:
    if route == "direct":
        return """

namespace EconCSLibEVEEntryGameDirectContract
open EconCSLibEVEEntryGameDirect

example (profile : PureProfile) :
    IsNash profile ↔
      profile = (.enter, .acquiesce) ∨
      profile = (.stayOut, .fight) := direct_nash_iff profile

example (profile : PureProfile) :
    IsSubgamePerfect profile ↔ profile = (.enter, .acquiesce) :=
  direct_subgamePerfect_iff profile

example : IsNash (.stayOut, .fight) ∧
    ¬ IsSubgamePerfect (.stayOut, .fight) :=
  direct_out_fight_separation

#print axioms EconCSLibEVEEntryGameDirect.direct_nash_iff
#print axioms EconCSLibEVEEntryGameDirect.direct_subgamePerfect_iff
#print axioms EconCSLibEVEEntryGameDirect.direct_out_fight_separation
end EconCSLibEVEEntryGameDirectContract
"""
    return """

namespace EconCSLibEVEEntryGameTransportContract
open EconCSLibEVEEntryGameTransport

example : RefinementCertificate := entryCertificate

example (profile : PureProfile) (player : Player) :
    normalPayoff profile player =
      AbstractTwoStage.payoff entryUtilities (encodeProfile profile) player :=
  payoff_preserved profile player

example : AbstractTwoStage.StrictEntryConditions entryUtilities :=
  hypothesis_bridge

example (profile : PureProfile) :
    IsNash profile ↔
      AbstractTwoStage.IsNash entryUtilities (encodeProfile profile) :=
  nash_preserved profile

example (profile : PureProfile) :
    IsSubgamePerfect profile ↔
      AbstractTwoStage.IsSubgamePerfect entryUtilities (encodeProfile profile) :=
  subgamePerfect_preserved profile

example (profile : PureProfile) :
    IsSubgamePerfect profile ↔ profile = (.enter, .acquiesce) :=
  transport_subgamePerfect_iff profile

example : IsNash (.stayOut, .fight) ∧
    ¬ IsSubgamePerfect (.stayOut, .fight) :=
  transport_out_fight_separation

#print axioms EconCSLibEVEEntryGameTransport.payoff_preserved
#print axioms EconCSLibEVEEntryGameTransport.hypothesis_bridge
#print axioms EconCSLibEVEEntryGameTransport.nash_preserved
#print axioms EconCSLibEVEEntryGameTransport.subgamePerfect_preserved
#print axioms EconCSLibEVEEntryGameTransport.entryCertificate
#print axioms EconCSLibEVEEntryGameTransport.abstract_nash_for_entry
#print axioms EconCSLibEVEEntryGameTransport.abstract_unique_spe_for_entry
#print axioms EconCSLibEVEEntryGameTransport.transport_subgamePerfect_iff
#print axioms EconCSLibEVEEntryGameTransport.transport_out_fight_separation
end EconCSLibEVEEntryGameTransportContract
"""


def _compile_source(source: str, *, name: str, temporary_root: Path):
    source_path = temporary_root / f"{name}.lean"
    source_path.write_text(source.rstrip() + "\n", encoding="utf-8")
    result = run(
        ["lake", "env", "lean", "-o", str(temporary_root / f"{name}.olean"),
         str(source_path)],
        cwd=REPO_ROOT,
        timeout=TIMEOUT_SECONDS,
    )
    warnings = sorted({
        line.strip() for line in result.output.splitlines()
        if "warning:" in line.lower()
    })
    return result, warnings


def _report(route: str, gates: dict[str, bool], failures: list[str],
            diagnostics: list[str], protected_before: dict[str, str],
            expected_protected_ok: bool,
            observed_axioms: list[str] | None = None) -> dict[str, Any]:
    try:
        protected_after = protected_hashes(_protected_paths(route))
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
        "task_id": "EVE-ENTRY-GAME-PAIRED-001",
        "route": route,
        "status": "passed" if passed else "failed",
        "score": 1.0 if passed else 0.0,
        "summary": (
            f"all deterministic Entry Game {route} route gates passed"
            if passed else f"one or more Entry Game {route} route gates failed"
        ),
        "gates": gates,
        "failure_codes": sorted(set(failures)),
        "diagnostics": diagnostics,
        "axioms": {
            "allowed": ALLOWED_AXIOMS,
            "observed": observed_axioms or [],
        },
        "environment": {
            "lean_toolchain": EXPECTED_TOOLCHAIN,
            "mathlib_commit": EXPECTED_MATHLIB_COMMIT,
            "allowed_imports": ALLOWED_IMPORTS,
            "warning_allowlist": [],
        },
    }


def evaluate_candidate(route: str, candidate_dir: Path,
                       baseline_dir: Path | None = None) -> dict[str, Any]:
    if route not in ROUTES:
        raise ValueError("unknown route")
    config = ROUTES[route]
    gates = {name: False for name in GATE_NAMES}
    failures: list[str] = []
    diagnostics: list[str] = []
    protected_before: dict[str, str] = {}
    expected_protected_ok = False
    try:
        candidate = safe_directory(candidate_dir, label="candidate directory",
                                   repository_root=REPO_ROOT)
        baseline = safe_directory(
            baseline_dir or _default_baseline(route),
            label="baseline directory", repository_root=REPO_ROOT,
        )
        case = load_json(_case_path(route))
        protected_before = protected_hashes(_protected_paths(route))
        protected_failures = _expected_protected_failures(case)
        expected_protected_ok = not protected_failures
        failures.extend(protected_failures)
        if failures:
            return _report(route, gates, failures, diagnostics,
                           protected_before, expected_protected_ok)
        gates["protected_assets_initial"] = True

        failures.extend(_case_contract_failures(case, route))
        failures.extend(boundary_failures(
            baseline, candidate, editable_file=EDITABLE_FILE
        ))
        if failures:
            return _report(route, gates, failures, diagnostics,
                           protected_before, expected_protected_ok)
        gates["boundary"] = True

        baseline_candidate = baseline / EDITABLE_FILE
        if case.get("seed_candidate_sha256") != sha256(baseline_candidate):
            failures.append("seed-candidate-hash-mismatch")
            return _report(route, gates, failures, diagnostics,
                           protected_before, expected_protected_ok)

        candidate_file = candidate / EDITABLE_FILE
        if candidate_file.stat().st_size > MAX_CANDIDATE_BYTES:
            failures.append("candidate-too-large")
            return _report(route, gates, failures, diagnostics,
                           protected_before, expected_protected_ok)
        source = candidate_file.read_text(encoding="utf-8")
        guard_module = load_guard_module(
            STATIC_GUARD, module_name=f"econcslib_entry_{route}_static_guard"
        )
        clean_source = guard_module.strip_comments_and_strings(source)
        gates["import_allowlist"] = source_imports(clean_source) == ALLOWED_IMPORTS
        if not gates["import_allowlist"]:
            failures.append("forbidden-import")
            return _report(route, gates, failures, diagnostics,
                           protected_before, expected_protected_ok)

        prefix = _task_prefix(source, config["marker"])
        gates["task_prefix"] = (
            prefix is not None and
            _sha256_text(prefix) == case.get("protected_prefix_sha256")
        )
        if not gates["task_prefix"]:
            failures.append("protected-task-prefix-changed")
            return _report(route, gates, failures, diagnostics,
                           protected_before, expected_protected_ok)

        guard = run([sys.executable, str(STATIC_GUARD), str(candidate_file)],
                    cwd=REPO_ROOT, timeout=TIMEOUT_SECONDS)
        gates["static_guard"] = guard.returncode == 0
        gates["trusted_bypass_guard"] = TRUST_BYPASS_PATTERN.search(clean_source) is None
        if not gates["static_guard"]:
            failures.append("forbidden-construct")
        if not gates["trusted_bypass_guard"]:
            failures.append("trusted-bypass")
        if failures:
            return _report(route, gates, failures, diagnostics,
                           protected_before, expected_protected_ok)

        raw_suffix = source.partition(config["marker"])[2]
        suffix = guard_module.strip_comments_and_strings(raw_suffix)
        gates["route_discipline"] = (
            all(token in suffix for token in config["required_source_tokens"])
            and all(token not in suffix for token in config["forbidden_source_tokens"])
        )
        if not gates["route_discipline"]:
            failures.append("route-discipline-violation")
            return _report(route, gates, failures, diagnostics,
                           protected_before, expected_protected_ok)

        environment_ok, environment_failures = _validate_environment()
        gates["environment"] = environment_ok
        failures.extend(environment_failures)
        if failures:
            return _report(route, gates, failures, diagnostics,
                           protected_before, expected_protected_ok)

        temp_parent = SIDECAR_ROOT / ".runtime" / "evaluator-tmp"
        temp_parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(
            prefix=f"entry-{route}-", dir=temp_parent
        ) as raw_temp:
            temporary_root = Path(raw_temp)
            compiled, candidate_warnings = _compile_source(
                source, name="Candidate", temporary_root=temporary_root
            )
            gates["compile"] = compiled.returncode == 0
            if not gates["compile"]:
                failures.append("compile-failed")
                output = normalize_output(compiled.output, temporary_root, REPO_ROOT)
                if output:
                    diagnostics.append(output[:1600])
                return _report(route, gates, failures, diagnostics,
                               protected_before, expected_protected_ok)

            contract, contract_warnings = _compile_source(
                source.rstrip() + _contract(route),
                name="RouteContract", temporary_root=temporary_root,
            )
            gates["target_declarations"] = contract.returncode == 0
            if not gates["target_declarations"]:
                failures.append("target-declaration-missing-or-wrong-type")
                output = normalize_output(contract.output, temporary_root, REPO_ROOT)
                if output:
                    diagnostics.append(output[:1600])
                return _report(route, gates, failures, diagnostics,
                               protected_before, expected_protected_ok)

            warnings = sorted(set(candidate_warnings + contract_warnings))
            gates["warning_policy"] = not warnings
            if warnings:
                failures.append("unexpected-warning")
                diagnostics.extend(warnings)
                return _report(route, gates, failures, diagnostics,
                               protected_before, expected_protected_ok)
            target_axioms = axioms(contract.output)
            unexpected_axioms = sorted(set(target_axioms) - set(ALLOWED_AXIOMS))
            gates["axiom_allowlist"] = not unexpected_axioms
            if unexpected_axioms:
                failures.append("target-axiom-outside-allowlist")
                diagnostics.append(
                    "unexpected target axioms: " + ", ".join(unexpected_axioms)
                )
            return _report(
                route, gates, failures, diagnostics, protected_before,
                expected_protected_ok, observed_axioms=target_axioms,
            )
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        failures.append(f"evaluator-input-error:{type(exc).__name__}")
    return _report(route, gates, failures, diagnostics,
                   protected_before, expected_protected_ok)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--route", choices=sorted(ROUTES), required=True)
    parser.add_argument("--candidate-dir", type=Path, required=True)
    parser.add_argument("--baseline-dir", type=Path)
    parser.add_argument("--score-output", type=Path)
    parser.add_argument("--report-output", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        report = evaluate_candidate(args.route, args.candidate_dir, args.baseline_dir)
    except Exception as exc:
        report = {
            "schema_version": "1.0.0", "task_id": "EVE-ENTRY-GAME-PAIRED-001",
            "route": args.route, "status": "failed", "score": 0.0,
            "summary": f"Entry Game {args.route} evaluator failed closed",
            "gates": {name: False for name in GATE_NAMES},
            "failure_codes": [f"evaluator-failed:{type(exc).__name__}"],
            "diagnostics": [],
        }
    if args.score_output is not None:
        write_score(args.score_output, report)
    if args.report_output is not None:
        write_report(args.report_output, report)
    print(f"Entry Game {args.route} evaluation: {report['status']} "
          f"(score={report['score']:.1f})")
    if report["failure_codes"]:
        print("Failure codes: " + ", ".join(report["failure_codes"]))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
