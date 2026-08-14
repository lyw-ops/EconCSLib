#!/usr/bin/env python3
"""Deterministically execute and validate Phase 4 REPAIR predictions.

Reference repairs are never used as an acceptance oracle. A candidate is
reconstructed inside its frozen public wrapper and checked against the public
edit contract, case-specific issue-resolution contract, Lean elaboration,
Mathlib linters, declaration type, axioms, and warnings.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

from phase4_harness import (
    HarnessFailure,
    PRIVATE_DEFAULT,
    REPO_ROOT,
    ROOT,
    compile_lean,
    guard_source,
    load_json,
    parse_axioms,
    require,
    run_text_linter,
    schema_validators,
    warning_lines,
)


DECLARATION_RE = re.compile(
    r"(?m)^\s*(?:public\s+|private\s+|protected\s+)?"
    r"(?:def|theorem|lemma|abbrev|opaque|instance|class|structure|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
TOKEN_RE = re.compile(r"[A-Za-z0-9_']+|[^\sA-Za-z0-9_]")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def edit_distance(left: list[str], right: list[str]) -> int:
    """Levenshtein edit count with one unit per insertion/deletion/substitution."""
    previous = list(range(len(right) + 1))
    for i, left_item in enumerate(left, 1):
        current = [i]
        for j, right_item in enumerate(right, 1):
            current.append(
                min(
                    current[-1] + 1,
                    previous[j] + 1,
                    previous[j - 1] + (left_item != right_item),
                )
            )
        previous = current
    return previous[-1]


def load_predictions(path: Path) -> list[dict[str, Any]]:
    validator = schema_validators()["prediction.schema.json"]
    paths = sorted(path.glob("*.json")) if path.is_dir() else [path]
    documents: list[dict[str, Any]] = []
    for candidate in paths:
        raw = load_json(candidate)
        batch = raw if isinstance(raw, list) else [raw]
        for document in batch:
            errors = list(validator.iter_errors(document))
            if errors:
                raise HarnessFailure(
                    f"invalid prediction in {candidate}: {errors[0].message}"
                )
            if document["task"] == "REPAIR":
                documents.append(document)
    return documents


def offset_position(text: str, offset: int) -> tuple[int, int]:
    prefix = text[:offset]
    line = prefix.count("\n") + 1
    column = len(prefix.rsplit("\n", 1)[-1]) + 1
    return line, column


def in_region(line: int, column: int, region: dict[str, Any]) -> bool:
    start = (region["start"]["line"], region["start"]["column"])
    end = (region["end"]["line"], region["end"]["column"])
    return start <= (line, column) <= end


def edit_contract_result(
    original: str, candidate: str, contract: dict[str, Any]
) -> dict[str, Any]:
    regions = contract["editable_regions"]
    matcher = difflib.SequenceMatcher(a=original, b=candidate, autojunk=False)
    outside: list[dict[str, Any]] = []
    for tag, i1, i2, _j1, _j2 in matcher.get_opcodes():
        if tag == "equal":
            continue
        offsets = range(i1, i2) if i1 != i2 else [i1]
        for offset in offsets:
            line, column = offset_position(original, min(offset, len(original)))
            if not any(in_region(line, column, region) for region in regions):
                outside.append({"line": line, "column": column, "operation": tag})

    changed_lines = edit_distance(original.splitlines(), candidate.splitlines())
    changed_tokens = edit_distance(TOKEN_RE.findall(original), TOKEN_RE.findall(candidate))
    original_declarations = DECLARATION_RE.findall(original)
    candidate_declarations = DECLARATION_RE.findall(candidate)
    declaration_gate = (
        contract["allow_new_declarations"]
        or candidate_declarations == original_declarations
    )
    import_gate = contract["allow_new_imports"] or not re.search(
        r"(?m)^\s*import\s", candidate
    )
    rename_gate = contract["allow_renaming"] or set(candidate_declarations) == set(
        original_declarations
    )
    budget = contract.get("max_changed_lines")
    budget_gate = budget is None or changed_lines <= budget
    return {
        "editable_regions_passed": not outside,
        "outside_edit_samples": outside[:10],
        "declaration_set_passed": declaration_gate,
        "import_permission_passed": import_gate,
        "rename_permission_passed": rename_gate,
        "change_budget_passed": budget_gate,
        "changed_lines": changed_lines,
        "changed_tokens": changed_tokens,
        "metric": contract["acceptance"]["edit_cost_metric"],
        "passed": not outside and declaration_gate and import_gate and rename_gate and budget_gate,
    }


def issue_resolution(case_id: str, candidate: str, linter_warnings: list[str]) -> dict[str, Any]:
    if case_id == "msb_r001":
        checks = {
            "missing_end_warning_absent": not any(
                "unclosed sections or namespaces" in warning for warning in linter_warnings
            )
        }
    elif case_id == "msb_r002":
        module_match = re.search(r"/-!(.*?)\-/", candidate, re.S)
        body = module_match.group(1) if module_match else ""
        lowered = body.casefold()
        semantic_anchor = any(
            anchor in lowered
            for anchor in ("reflexiv", "le_refl_pilot", "n ≤ n", "`≤`", "natural-number order")
        )
        prose_words = re.findall(r"[A-Za-z]+", body)
        checks = {
            "module_docstring_present": module_match is not None,
            "editorial_placeholder_removed": "must be updated" not in lowered,
            "mathematical_summary_present": semantic_anchor and len(prose_words) >= 6,
        }
    elif case_id == "msb_r003":
        checks = {
            "existing_api_lemma_used": "map_subtype_inj" in candidate,
            "expanded_internal_reconstruction_removed": "Subgroup.map_injective" not in candidate,
        }
    else:
        raise HarnessFailure(f"no deterministic issue-resolution contract for {case_id}")
    return {"checks": checks, "passed": all(checks.values())}


def splice_candidate_wrapper(
    case_id: str, wrapper: str, original: str, candidate: str
) -> str:
    """Embed the public repair payload while retaining the hidden compile wrapper."""
    if case_id == "msb_r001":
        require(wrapper.count(original) == 1, f"public wrapper splice is ambiguous: {case_id}")
        return wrapper.replace(original, candidate)
    if case_id == "msb_r002":
        original_doc = re.search(r"/-!.*?\-/", original, re.S)
        candidate_doc = re.search(r"/-!.*?\-/", candidate, re.S)
        require(original_doc is not None and candidate_doc is not None,
                "msb_r002 candidate must retain a module docstring")
        original_decl = original[original_doc.end():].strip()
        candidate_decl = candidate[candidate_doc.end():].strip()
        require(wrapper.count(original_doc.group()) == 1 and wrapper.count(original_decl) == 1,
                "msb_r002 wrapper splice is ambiguous")
        return wrapper.replace(original_doc.group(), candidate_doc.group()).replace(
            original_decl, candidate_decl
        )
    if case_id == "msb_r003":
        marker = ":= by"
        require(marker in original and marker in candidate, "msb_r003 proof marker is missing")
        original_proof = original[original.index(marker):]
        candidate_proof = candidate[candidate.index(marker):]
        require(wrapper.count(original_proof) == 1, "msb_r003 wrapper splice is ambiguous")
        return wrapper.replace(original_proof, candidate_proof)
    raise HarnessFailure(f"no wrapper splice contract for {case_id}")


def lake_linter_environment(timeout: int) -> tuple[dict[str, str], Path]:
    build = subprocess.run(
        ["lake", "build", "mathlib:lint-style"], cwd=REPO_ROOT, text=True,
        capture_output=True, check=False, timeout=timeout,
    )
    require(build.returncode == 0, f"could not build lint-style: {build.stderr}")
    executable = (
        REPO_ROOT / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "bin" /
        "lint-style"
    )
    environment = subprocess.run(
        ["lake", "env", "env"], cwd=REPO_ROOT, text=True,
        capture_output=True, check=False, timeout=timeout,
    )
    require(environment.returncode == 0, "could not capture Lake environment")
    values = os.environ.copy()
    values.update(line.split("=", 1) for line in environment.stdout.splitlines() if "=" in line)
    return values, executable


def evaluate_one(
    prediction: dict[str, Any], timeout: int, lake_environment: dict[str, str],
    lint_executable: Path, output_root: Path,
) -> dict[str, Any]:
    case_id = prediction["case_id"]
    public_path = next(iter((ROOT / "cases" / "repair" / case_id).glob("public.json")))
    public = load_json(public_path)
    original_snippet = public["prompt"]["code"]
    candidate_snippet = prediction["repaired_code"]
    candidate_hash = sha256_text(candidate_snippet)
    if prediction["answerability"] == "INSUFFICIENT_CONTEXT":
        passed = candidate_snippet == ""
        return {
            "case_id": case_id,
            "candidate_sha256": candidate_hash,
            "accepted": passed,
            "insufficient_context_abstention": passed,
            "reference_text_match_diagnostic_only": False,
        }

    contract = public["prompt"]["edit_contract"]
    edit = edit_contract_result(original_snippet, candidate_snippet, contract)
    wrapper_path = public_path.parent / "prompt" / "Case.lean"
    wrapper = wrapper_path.read_text(encoding="utf-8")
    candidate_source_text = splice_candidate_wrapper(
        case_id, wrapper, original_snippet, candidate_snippet
    )
    spec = load_json(PRIVATE_DEFAULT / "validation-specs" / f"{case_id}.json")
    target = spec["statement_target"]
    log_dir = output_root / "logs" / case_id / candidate_hash
    log_dir.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory(prefix=".mathlib-style-repair-", dir=REPO_ROOT) as raw, \
            tempfile.TemporaryDirectory(prefix="MathlibStyleRepairLint", dir=REPO_ROOT) as lint_raw:
        temp = Path(raw)
        candidate_source = temp / f"{case_id}-candidate.lean"
        candidate_source.write_text(candidate_source_text, encoding="utf-8")
        static_passed = True
        static_error = ""
        try:
            guard_source(candidate_source)
        except HarnessFailure as exc:
            static_passed = False
            static_error = str(exc)

        result = compile_lean(candidate_source, temp / "candidate.olean", temp, timeout)
        checker = compile_lean(candidate_source, temp / "candidate-checker.olean", temp, timeout)
        linter = compile_lean(
            candidate_source, temp / "candidate-linter.olean", temp, timeout,
            ["-D", "linter.mathlibStandardSet=true"],
        )
        text_linter = run_text_linter(
            candidate_source, Path(lint_raw), timeout, lake_environment, lint_executable
        )
        warnings = warning_lines(linter.stdout + linter.stderr)
        whitelist = spec.get("warning_whitelist", [])
        unexpected = [
            warning for warning in warnings
            if not any(allowed in warning for allowed in whitelist)
        ]

        baseline_probe = temp / "baseline-axioms.lean"
        baseline_probe.write_text(wrapper + f"\n#print axioms {target}\n", encoding="utf-8")
        baseline_axiom_result = compile_lean(
            baseline_probe, temp / "baseline-axioms.olean", temp, timeout
        )
        candidate_probe = temp / "candidate-axioms.lean"
        candidate_probe.write_text(
            candidate_source_text + f"\n#print axioms {target}\n", encoding="utf-8"
        )
        candidate_axiom_result = compile_lean(
            candidate_probe, temp / "candidate-axioms.olean", temp, timeout
        )
        baseline_axioms = parse_axioms(
            baseline_axiom_result.stdout + baseline_axiom_result.stderr
        )
        observed_axioms = parse_axioms(
            candidate_axiom_result.stdout + candidate_axiom_result.stderr
        )
        axiom_delta = sorted(set(observed_axioms) - set(baseline_axioms))

        type_outputs = []
        type_results = []
        for label, source_text in (("baseline", wrapper), ("candidate", candidate_source_text)):
            probe = temp / f"{label}-type.lean"
            probe.write_text(source_text + f"\n#check {target}\n", encoding="utf-8")
            probe_result = compile_lean(probe, temp / f"{label}-type.olean", temp, timeout)
            type_results.append(probe_result)
            type_outputs.append(probe_result.stdout + probe_result.stderr)

        issue = issue_resolution(case_id, candidate_snippet, warnings)
        compile_passed = result.exit_code == checker.exit_code == 0
        reproducible = (
            result.stdout + result.stderr == checker.stdout + checker.stderr
        )
        linter_passed = linter.exit_code == 0 and text_linter.exit_code == 0
        axiom_passed = (
            baseline_axiom_result.exit_code == candidate_axiom_result.exit_code == 0
            and not axiom_delta
        )
        statement_passed = (
            all(probe.exit_code == 0 for probe in type_results)
            and type_outputs[0] == type_outputs[1]
        )
        warning_passed = not unexpected
        no_new_findings = linter_passed and warning_passed and issue["passed"]
        gates = {
            "edit_contract": edit["passed"],
            "static_guard": static_passed,
            "compile": compile_passed,
            "repeat_elaboration": reproducible,
            "standard_and_text_linters": linter_passed,
            "target_issue_resolved": issue["passed"],
            "statement_preserved": statement_passed,
            "axiom_delta_empty": axiom_passed,
            "warning_policy": warning_passed,
            "no_new_findings": no_new_findings,
        }
        streams = {
            "compile.stdout": result.raw_stdout,
            "compile.stderr": result.raw_stderr,
            "checker.stdout": checker.raw_stdout,
            "checker.stderr": checker.raw_stderr,
            "standard-linter.stdout": linter.raw_stdout,
            "standard-linter.stderr": linter.raw_stderr,
            "text-linter.stdout": text_linter.raw_stdout,
            "text-linter.stderr": text_linter.raw_stderr,
            "baseline-axioms.stdout": baseline_axiom_result.raw_stdout,
            "baseline-axioms.stderr": baseline_axiom_result.raw_stderr,
            "candidate-axioms.stdout": candidate_axiom_result.raw_stdout,
            "candidate-axioms.stderr": candidate_axiom_result.raw_stderr,
            "baseline-type.stdout": type_results[0].raw_stdout,
            "baseline-type.stderr": type_results[0].raw_stderr,
            "candidate-type.stdout": type_results[1].raw_stdout,
            "candidate-type.stderr": type_results[1].raw_stderr,
        }
        hashes = {}
        for name, content in streams.items():
            path = log_dir / name
            path.write_text(content, encoding="utf-8")
            hashes[name] = hashlib.sha256(content.encode()).hexdigest()

    reference_match = any(
        "\n".join(line.rstrip() for line in candidate_snippet.strip().splitlines())
        == "\n".join(line.rstrip() for line in reference.strip().splitlines())
        for reference in load_json(PRIVATE_DEFAULT / "gold" / f"{case_id}.json")["reference_repairs"]
    )
    return {
        "case_id": case_id,
        "candidate_sha256": candidate_hash,
        "accepted": all(gates.values()),
        "gates": gates,
        "edit_cost": edit,
        "issue_resolution": issue,
        "static_guard_error": static_error,
        "axioms": {
            "baseline": baseline_axioms,
            "observed": observed_axioms,
            "delta": axiom_delta,
        },
        "warnings": {"observed": warnings, "whitelist": whitelist, "unexpected": unexpected},
        "log_sha256": hashes,
        "reference_text_match_diagnostic_only": reference_match,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=PRIVATE_DEFAULT / "scoring" / "repair-evaluations.json",
    )
    parser.add_argument("--timeout", type=int, default=90)
    parser.add_argument(
        "--output-root", type=Path, default=PRIVATE_DEFAULT / "scoring" / "repair-evaluation"
    )
    args = parser.parse_args()
    try:
        predictions = load_predictions(args.predictions)
        require(predictions, "no REPAIR predictions found")
        lake_environment, lint_executable = lake_linter_environment(args.timeout)
        results = [
            evaluate_one(
                prediction, args.timeout, lake_environment, lint_executable, args.output_root
            )
            for prediction in predictions
        ]
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(
                {"repair_evaluator_version": "1.0.0", "results": results},
                ensure_ascii=False,
                indent=2,
            ) + "\n",
            encoding="utf-8",
        )
        print(f"repair evaluation passed: {sum(r['accepted'] for r in results)}/{len(results)}")
        return 0 if all(result["accepted"] for result in results) else 1
    except (HarnessFailure, OSError, subprocess.TimeoutExpired) as exc:
        print(f"repair evaluation failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
