#!/usr/bin/env python3
"""Phase 4 benchmark hard gates for public cases and private custody artifacts.

The harness is intentionally offline: every JSON Schema reference is resolved from
the frozen local schema directory, and every Lean output is written to a temporary
directory inside the Lake project before being removed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import platform
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = ROOT.parents[1]
SCHEMA_DIR = ROOT / "manifests" / "schemas"
PRIVATE_DEFAULT = ROOT / "heldout" / "private"
EXPECTED_LEAN = "version 4.30.0"
EXPECTED_MATHLIB_COMMIT = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
PRIMARY_TASK_COUNTS = {"PAIR": 6, "DETECT": 4, "REPAIR": 3, "LOCATE": 3}
LEAK_PATTERNS = {
    "GitHub URL": re.compile(r"https?://(?:www\.)?github\.com", re.I),
    "pull-request reference": re.compile(r"(?i)\b(?:pull request|PR)\s*#?\d+|/pull/\d+"),
    "40-character commit": re.compile(r"(?<![0-9a-f])[0-9a-f]{40}(?![0-9a-f])", re.I),
    "review thread/comment identifier": re.compile(
        r"(?i)(?:discussion_r|issuecomment-|PRRT_|PRRC_)\w+"
    ),
    "private answerability label": re.compile(
        r"\b(?:ANSWERABLE|MULTIPLE_ACCEPTABLE|INSUFFICIENT_CONTEXT)\b"
    ),
    "private custody path": re.compile(r"heldout/private"),
    "gold/adjudication field or phrase": re.compile(
        r"(?i)(?:gold answer|reference[ _]repairs?|adjudication|"
        r"accepted_verdicts|accepted_location_ids|preferred_location_ids)"
    ),
}


class HarnessFailure(RuntimeError):
    """A deterministic hard-gate failure."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise HarnessFailure(message)


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise HarnessFailure(f"cannot load {path}: {exc}") from exc


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def schema_runtime() -> tuple[Any, Any, Any]:
    try:
        from jsonschema import Draft202012Validator, FormatChecker
        from referencing import Registry, Resource
    except ImportError as exc:
        raise HarnessFailure(
            "Phase 4 requires the standard jsonschema runtime; install "
            "benchmarks/mathlib-style/requirements-phase4.txt"
        ) from exc
    return Draft202012Validator, FormatChecker, (Registry, Resource)


def schema_validators() -> dict[str, Any]:
    Draft202012Validator, FormatChecker, registry_types = schema_runtime()
    Registry, Resource = registry_types
    registry = Registry()
    schemas: dict[str, Any] = {}
    for path in sorted(SCHEMA_DIR.glob("*.schema.json")):
        schema = load_json(path)
        Draft202012Validator.check_schema(schema)
        schemas[path.name] = schema
        registry = registry.with_resource(schema["$id"], Resource.from_contents(schema))
    return {
        name: Draft202012Validator(
            schema, registry=registry, format_checker=FormatChecker()
        )
        for name, schema in schemas.items()
    }


def validate_document(path: Path, validator: Any) -> None:
    errors = sorted(validator.iter_errors(load_json(path)), key=lambda error: list(error.path))
    if errors:
        details = "; ".join(f"{error.json_path}: {error.message}" for error in errors)
        raise HarnessFailure(f"schema validation failed for {path}: {details}")


def public_case_paths() -> list[Path]:
    return sorted((ROOT / "cases").glob("*/*/public.json"))


def case_dir(case_id: str) -> Path:
    matches = list((ROOT / "cases").glob(f"*/{case_id}"))
    require(len(matches) == 1, f"expected exactly one directory for {case_id}")
    return matches[0]


def validate_public_layout(validators: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    manifest = load_json(ROOT / "manifests" / "PILOT_CASES.json")
    primary_ids = manifest["primary_case_ids"]
    require(len(primary_ids) == 16 and len(set(primary_ids)) == 16, "primary case list must have 16 IDs")
    groups = manifest["stratum_groups"]
    require(set(groups) == {"surface", "documentation_statement", "proof", "api_integration"},
            "stratum group names changed")
    require(all(len(ids) == 4 and len(set(ids)) == 4 for ids in groups.values()),
            "each stratum group must contain four distinct primary cases")
    require(set().union(*(set(ids) for ids in groups.values())) == set(primary_ids),
            "stratum groups must cover the primary set exactly")

    documents: dict[str, Any] = {}
    for path in public_case_paths():
        validate_document(path, validators["public-case.schema.json"])
        document = load_json(path)
        require(document["id"] == path.parent.name, f"case ID/path mismatch: {path}")
        require("answerability" not in document["requested_output"],
                f"public requested_output leaks private answerability: {path}")
        require("answerability" not in document,
                f"public case leaks private answerability: {path}")
        require((path.parent / "prompt" / "Case.lean").is_file(), f"missing Case.lean: {path.parent}")
        require((path.parent / "README.md").is_file(), f"missing README: {path.parent}")
        files = {
            str(candidate.relative_to(path.parent))
            for candidate in path.parent.rglob("*")
            if candidate.is_file()
        }
        require(
            files == {"public.json", "README.md", "prompt/Case.lean"},
            f"public case layout contains unexpected assets: {path.parent}: {sorted(files)}",
        )
        documents[document["id"]] = document

    mirrors = manifest["pair_mirrors"]
    require(len(mirrors) == 6, "every PAIR case must have one mirror")
    require(set(documents) == set(primary_ids) | set(mirrors.values()),
            "public case directories differ from the frozen primary+mirror inventory")
    public_hashes = manifest.get("public_case_sha256")
    require(isinstance(public_hashes, dict) and set(public_hashes) == set(documents),
            "PILOT_CASES public hashes must cover every primary and mirror exactly")
    for case_id, expected_hashes in public_hashes.items():
        directory = case_dir(case_id)
        assets = {
            "public_json": directory / "public.json",
            "prompt": directory / "prompt" / "Case.lean",
            "readme": directory / "README.md",
        }
        require(set(expected_hashes) == set(assets), f"public hash keys drifted: {case_id}")
        for label, asset in assets.items():
            require(
                sha256_file(asset) == expected_hashes[label],
                f"PILOT_CASES public hash drift: {case_id}:{label}",
            )
    counts = Counter(documents[case_id]["task"] for case_id in primary_ids)
    require(dict(counts) == PRIMARY_TASK_COUNTS, f"primary task counts differ: {dict(counts)}")
    for original_id, mirror_id in mirrors.items():
        original, mirror = documents[original_id], documents[mirror_id]
        require(original["task"] == mirror["task"] == "PAIR", f"non-PAIR mirror: {original_id}")
        require(original["prompt"]["candidate_a"] == mirror["prompt"]["candidate_b"],
                f"mirror B is not original A: {mirror_id}")
        require(original["prompt"]["candidate_b"] == mirror["prompt"]["candidate_a"],
                f"mirror A is not original B: {mirror_id}")
        require((case_dir(original_id) / "prompt" / "Case.lean").read_bytes()
                == (case_dir(mirror_id) / "prompt" / "Case.lean").read_bytes(),
                f"PAIR mirror wrapper drifted: {mirror_id}")
    return manifest, documents


def scan_public_leakage() -> None:
    for path in sorted((ROOT / "cases").rglob("*")):
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for label, pattern in LEAK_PATTERNS.items():
            require(pattern.search(text) is None, f"public leakage ({label}) in {path}")
    private = ROOT / "heldout" / "private"
    check = subprocess.run(
        ["git", "check-ignore", "-q", str(private / "sentinel.json")],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    require(check.returncode == 0, "heldout/private is not ignored by Git")
    generated = [
        str(path.relative_to(ROOT))
        for suffix in ("*.olean", "*.ilean")
        for path in ROOT.rglob(suffix)
    ]
    require(not generated, f"generated Lean artifacts in benchmark tree: {generated}")


def validate_private(validators: dict[str, Any], private_root: Path) -> int:
    if not private_root.exists():
        return 0
    schemas = {
        "gold": "private-gold.schema.json",
        "provenance": "private-provenance.schema.json",
        "annotations": "annotation.schema.json",
        "validation": "validation-record.schema.json",
    }
    validated = 0
    for directory, schema_name in schemas.items():
        for path in sorted((private_root / directory).rglob("*.json")):
            validate_document(path, validators[schema_name])
            validated += 1
    return validated


def normalize_output(text: str, temp_root: Path) -> str:
    normalized = text.replace(str(REPO_ROOT), "<REPO>").replace(str(temp_root), "<TMP>")
    normalized = re.sub(r"\b\d+(?:\.\d+)?(?:ms|s)\b", "<TIME>", normalized)
    return normalized.replace("\\", "/")


def warning_lines(text: str) -> list[str]:
    return sorted({line.strip() for line in text.splitlines() if "warning:" in line.lower()})


def guard_source(path: Path) -> None:
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "static_lean_guard.py"), str(path)],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    require(result.returncode == 0, f"placeholder/static guard failed for {path}: {result.stderr.strip()}")


@dataclass
class CompileResult:
    command: str
    exit_code: int
    duration_ms: int
    stdout: str
    stderr: str
    raw_stdout: str
    raw_stderr: str


def compile_lean(
    source: Path,
    output: Path,
    temp_root: Path,
    timeout: int,
    lean_options: list[str] | None = None,
) -> CompileResult:
    command = ["lake", "env", "lean", *(lean_options or []), "-o", str(output), str(source)]
    started = time.monotonic()
    try:
        result = subprocess.run(
            command,
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=False,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        raise HarnessFailure(f"Lean timeout after {timeout}s: {source}") from exc
    return CompileResult(
        command=" ".join(command),
        exit_code=result.returncode,
        duration_ms=round((time.monotonic() - started) * 1000),
        stdout=normalize_output(result.stdout, temp_root),
        stderr=normalize_output(result.stderr, temp_root),
        raw_stdout=result.stdout,
        raw_stderr=result.stderr,
    )


def run_text_linter(
    source: Path,
    lint_root: Path,
    timeout: int,
    lake_environment: dict[str, str],
) -> CompileResult:
    """Run Mathlib's pinned text-based linter suite on one isolated source copy."""
    lint_source = lint_root / "EconCSLib" / f"{source.parent.parent.name}.lean"
    lint_source.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, lint_source)
    for workspace_file in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        shutil.copyfile(REPO_ROOT / workspace_file, lint_root / workspace_file)
    if not (lint_root / ".lake").exists():
        os.symlink(REPO_ROOT / ".lake", lint_root / ".lake", target_is_directory=True)
    lint_scripts = lint_root / "scripts"
    lint_scripts.mkdir(exist_ok=True)
    shutil.copyfile(
        REPO_ROOT / ".lake" / "packages" / "mathlib" / "scripts" / "nolints-style.txt",
        lint_scripts / "nolints-style.txt",
    )
    module_name = f"EconCSLib.{lint_source.stem}"
    command = ["lake", "exe", "lint-style", module_name]
    run_environment = dict(lake_environment)
    run_environment["PWD"] = str(lint_root)
    run_environment["LEAN_SRC_PATH"] = os.pathsep.join(
        str(lint_root) if entry == str(REPO_ROOT) else entry
        for entry in run_environment.get("LEAN_SRC_PATH", "").split(os.pathsep)
    )
    started = time.monotonic()
    try:
        result = subprocess.run(
            command,
            cwd=lint_root,
            text=True,
            capture_output=True,
            check=False,
            timeout=timeout,
            env=run_environment,
        )
    except subprocess.TimeoutExpired as exc:
        raise HarnessFailure(f"text-linter timeout after {timeout}s: {source}") from exc
    return CompileResult(
        command=" ".join(command),
        exit_code=result.returncode,
        duration_ms=round((time.monotonic() - started) * 1000),
        stdout=normalize_output(result.stdout, lint_root),
        stderr=normalize_output(result.stderr, lint_root),
        raw_stdout=result.stdout,
        raw_stderr=result.stderr,
    )


def parse_axioms(text: str) -> list[str]:
    found: set[str] = set()
    for match in re.finditer(r"depends on axioms:\s*\[([^\]]*)\]", text, re.S):
        found.update(item.strip() for item in match.group(1).split(",") if item.strip())
    return sorted(found)


def run_location_probe(
    source: Path,
    temp_root: Path,
    timeout: int,
    targets: list[dict[str, str]],
) -> CompileResult | None:
    """Run applicable ``#find_home`` evidence without treating it as human gold."""
    if not targets:
        return None
    commands = []
    for target in targets:
        declaration = target.get("declaration")
        expected_module = target.get("expected_module")
        require(isinstance(declaration, str) and declaration,
                "location probe declaration is missing")
        require(isinstance(expected_module, str) and expected_module,
                f"location probe expected module is missing: {declaration}")
        commands.append(f"#find_home {declaration}")
    probe = temp_root / f"{source.parent.parent.name}-find-home.lean"
    probe.write_text(
        source.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n",
        encoding="utf-8",
    )
    result = compile_lean(
        probe,
        temp_root / f"{source.parent.parent.name}-find-home.olean",
        temp_root,
        timeout,
    )
    require(result.exit_code == 0,
            f"#find_home probe failed for {source.parent.parent.name}:\n"
            f"{result.stdout}{result.stderr}")
    combined = result.stdout + result.stderr
    for target in targets:
        require(target["expected_module"] in combined,
                f"#find_home evidence drift for {source.parent.parent.name}: "
                f"{target['declaration']}")
    return result


def validation_spec(private_root: Path, case_id: str) -> dict[str, Any]:
    path = private_root / "validation-specs" / f"{case_id}.json"
    return load_json(path) if path.is_file() else {}


def write_validation_record(
    private_root: Path,
    case_id: str,
    result: CompileResult,
    checker: CompileResult,
    baseline_axioms: list[str],
    observed_axioms: list[str],
    warnings: list[str],
    baseline_warnings: list[str],
    whitelist: list[str],
    source_hash: str,
    stdout_hash: str,
    stderr_hash: str,
    statement_preserved: bool | None,
    extra_validator_ids: list[str],
    log_artifacts: dict[str, str],
) -> Path:
    logs = private_root / "logs" / case_id
    records = private_root / "validation"
    logs.mkdir(parents=True, exist_ok=True)
    records.mkdir(parents=True, exist_ok=True)
    for name, content in log_artifacts.items():
        (logs / name).write_text(content, encoding="utf-8")
    stdout_path, stderr_path = logs / "compile.stdout", logs / "compile.stderr"
    standard_members = load_json(ROOT / "manifests" / "VALIDATORS.json")[
        "standard_set_exact_members"
    ]
    executed_validators = [
        {"validator_id": member, "findings": []} for member in standard_members
    ]
    additional_executed = [
        "compiler.lean",
        "custom.staticPlaceholderAndNativeGuard",
        "command.printAxioms",
        "checker.independentLeanElaboration",
        "linter.unicodeLinter",
        *(validator_id for validator_id in extra_validator_ids
          if not validator_id.startswith("human.")),
    ]
    already_recorded = set(standard_members)
    for validator_id in additional_executed:
        if validator_id not in already_recorded:
            executed_validators.append({"validator_id": validator_id, "findings": []})
            already_recorded.add(validator_id)
    executed_validators.append(
        {"validator_id": "linter.mathlibStandardSet", "findings": warnings}
    )
    executed_validators.append(
        {"validator_id": "baseline.linter.mathlibStandardSet", "findings": baseline_warnings}
    )
    record = {
        "schema_version": "0.3.0",
        "case_id": case_id,
        "artifact_id": "reference-repair" if statement_preserved is not None else "public-prompt",
        "compile": {
            "command": result.command.replace(str(REPO_ROOT), "<REPO>"),
            "exit_code": result.exit_code,
            "duration_ms": result.duration_ms,
            "stdout_path": str(stdout_path.relative_to(private_root)),
            "stderr_path": str(stderr_path.relative_to(private_root)),
        },
        "placeholder_guards": {
            "contains_sorry": False,
            "contains_admit": False,
            "introduced_forbidden_declarations": [],
        },
        "axioms": {
            "baseline": baseline_axioms,
            "observed": observed_axioms,
            "delta": sorted(set(observed_axioms) - set(baseline_axioms)),
        },
        "warnings": {"observed": warnings, "whitelist": whitelist, "unexpected": []},
        "linters": executed_validators,
        "statement_preserved": statement_preserved,
        "hashes": {
            "source": f"sha256:{source_hash}",
            "stdout": f"sha256:{stdout_hash}",
            "stderr": f"sha256:{stderr_hash}",
            "checker_stdout": f"sha256:{sha256_bytes(checker.raw_stdout.encode())}",
            "checker_stderr": f"sha256:{sha256_bytes(checker.raw_stderr.encode())}",
            **{
                "log_" + re.sub(r"[^a-zA-Z0-9]+", "_", name).strip("_"):
                    f"sha256:{sha256_bytes(content.encode())}"
                for name, content in sorted(log_artifacts.items())
            },
        },
        "tool_versions": {
            "harness": "0.3.0",
            "mathlib_release": "v4.30.0",
            "mathlib_commit": EXPECTED_MATHLIB_COMMIT,
            "lean_toolchain": "leanprover/lean4:v4.30.0",
        },
    }
    path = records / f"{case_id}.json"
    path.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return path


def compile_cases(
    manifest: dict[str, Any],
    validators: dict[str, Any],
    private_root: Path,
    timeout: int,
    write_records: bool,
) -> int:
    version = subprocess.run(
        ["lake", "env", "lean", "--version"], cwd=REPO_ROOT, text=True,
        capture_output=True, check=False, timeout=timeout,
    )
    require(version.returncode == 0 and EXPECTED_LEAN in version.stdout,
            f"expected Lean 4.30.0, got {(version.stdout + version.stderr).strip()}")
    lint_build = subprocess.run(
        ["lake", "build", "mathlib:lint-style"], cwd=REPO_ROOT, text=True,
        capture_output=True, check=False, timeout=timeout,
    )
    require(lint_build.returncode == 0,
            f"could not build pinned lint-style executable: {lint_build.stderr.strip()}")
    environment_result = subprocess.run(
        ["lake", "env", "env"], cwd=REPO_ROOT, text=True,
        capture_output=True, check=False, timeout=timeout,
    )
    require(environment_result.returncode == 0, "could not capture pinned Lake environment")
    lake_environment = os.environ.copy()
    lake_environment.update(
        line.split("=", 1) for line in environment_result.stdout.splitlines() if "=" in line
    )
    cases = sorted(public_case_paths())
    compiled = 0
    with tempfile.TemporaryDirectory(prefix=".mathlib-style-phase4-", dir=REPO_ROOT) as raw_temp, \
            tempfile.TemporaryDirectory(prefix="MathlibStylePhase4Lint", dir=REPO_ROOT) as raw_lint:
        temp_root = Path(raw_temp)
        lint_root = Path(raw_lint)
        for public_path in cases:
            case_id = public_path.parent.name
            source = public_path.parent / "prompt" / "Case.lean"
            case_temp_root = temp_root / case_id
            case_lint_root = lint_root / case_id
            case_temp_root.mkdir()
            guard_source(source)
            result = compile_lean(
                source, case_temp_root / f"{case_id}.olean", case_temp_root, timeout
            )
            require(result.exit_code == 0,
                    f"Lean compilation failed for {case_id}:\n{result.stdout}{result.stderr}")
            checker = compile_lean(
                source,
                case_temp_root / f"{case_id}-checker.olean",
                case_temp_root,
                timeout,
            )
            require(checker.exit_code == 0,
                    f"independent checker compilation failed for {case_id}:\n{checker.stdout}{checker.stderr}")
            require(sha256_bytes((result.stdout + result.stderr).encode())
                    == sha256_bytes((checker.stdout + checker.stderr).encode()),
                    f"non-reproducible normalized compiler output for {case_id}")

            linter_result = compile_lean(
                source,
                case_temp_root / f"{case_id}-linters.olean",
                case_temp_root,
                timeout,
                ["-D", "linter.mathlibStandardSet=true"],
            )
            require(linter_result.exit_code == 0,
                    f"standard linter elaboration failed for {case_id}:\n"
                    f"{linter_result.stdout}{linter_result.stderr}")
            text_linter_result = run_text_linter(
                source, case_lint_root, timeout, lake_environment
            )
            require(text_linter_result.exit_code == 0,
                    f"text/Unicode linter failed for {case_id}:\n"
                    f"{text_linter_result.stdout}{text_linter_result.stderr}")

            targets = manifest["declaration_targets"].get(case_id, [])
            probe_text = source.read_text(encoding="utf-8") + "\n" + "\n".join(
                f"#print axioms {target}" for target in targets
            ) + "\n"
            probe = case_temp_root / f"{case_id}-axioms.lean"
            probe.write_text(probe_text, encoding="utf-8")
            probe_result = compile_lean(
                probe,
                case_temp_root / f"{case_id}-axioms.olean",
                case_temp_root,
                timeout,
            )
            require(probe_result.exit_code == 0,
                    f"axiom probe failed for {case_id}:\n{probe_result.stdout}{probe_result.stderr}")
            baseline_axioms = parse_axioms(probe_result.stdout + probe_result.stderr)

            observed_warnings = warning_lines(linter_result.stdout + linter_result.stderr)
            baseline_warnings = observed_warnings
            baseline_result = result
            baseline_checker = checker
            baseline_linter_result = linter_result
            baseline_text_linter_result = text_linter_result
            baseline_probe_result = probe_result
            spec = validation_spec(private_root, case_id)
            location_probe_result = run_location_probe(
                source, case_temp_root, timeout, spec.get("location_probe_targets", [])
            )
            observed_axioms = baseline_axioms
            statement_preserved: bool | None = None
            validated_source = source
            type_results: list[tuple[str, CompileResult]] = []
            after_relative = spec.get("after_path")
            if after_relative:
                after = private_root / after_relative
                validated_source = after
                require(after.is_file(), f"reference repair missing for {case_id}: {after_relative}")
                guard_source(after)
                result = compile_lean(
                    after,
                    case_temp_root / f"{case_id}-after.olean",
                    case_temp_root,
                    timeout,
                )
                require(result.exit_code == 0,
                        f"reference repair compilation failed for {case_id}:\n{result.stdout}{result.stderr}")
                checker = compile_lean(
                    after,
                    case_temp_root / f"{case_id}-after-checker.olean",
                    case_temp_root,
                    timeout,
                )
                require(checker.exit_code == 0,
                        f"reference repair checker failed for {case_id}:\n{checker.stdout}{checker.stderr}")
                require(sha256_bytes((result.stdout + result.stderr).encode())
                        == sha256_bytes((checker.stdout + checker.stderr).encode()),
                        f"non-reproducible reference-repair output for {case_id}")
                linter_result = compile_lean(
                    after,
                    case_temp_root / f"{case_id}-after-linters.olean",
                    case_temp_root,
                    timeout,
                    ["-D", "linter.mathlibStandardSet=true"],
                )
                require(linter_result.exit_code == 0,
                        f"reference repair standard linter failed for {case_id}")
                text_linter_result = run_text_linter(
                    after, case_lint_root, timeout, lake_environment
                )
                require(text_linter_result.exit_code == 0,
                        f"reference repair text/Unicode linter failed for {case_id}:\n"
                        f"{text_linter_result.stdout}{text_linter_result.stderr}")

                after_probe = case_temp_root / f"{case_id}-after-axioms.lean"
                after_probe.write_text(
                    after.read_text(encoding="utf-8") + "\n" + "\n".join(
                        f"#print axioms {target}" for target in targets
                    ) + "\n",
                    encoding="utf-8",
                )
                after_probe_result = compile_lean(
                    after_probe,
                    case_temp_root / f"{case_id}-after-axioms.olean",
                    case_temp_root,
                    timeout,
                )
                require(after_probe_result.exit_code == 0,
                        f"reference-repair axiom probe failed for {case_id}")
                observed_axioms = parse_axioms(
                    after_probe_result.stdout + after_probe_result.stderr
                )
                require(not (set(observed_axioms) - set(baseline_axioms)),
                        f"reference repair introduces axioms for {case_id}")

                target = spec.get("statement_target")
                require(isinstance(target, str) and target, f"statement target missing for {case_id}")
                type_outputs = []
                for label, candidate in (("before", source), ("after", after)):
                    type_probe = case_temp_root / f"{case_id}-{label}-type.lean"
                    type_probe.write_text(
                        candidate.read_text(encoding="utf-8") + f"\n#check {target}\n",
                        encoding="utf-8",
                    )
                    type_result = compile_lean(
                        type_probe,
                        case_temp_root / f"{case_id}-{label}-type.olean",
                        case_temp_root,
                        timeout,
                    )
                    require(type_result.exit_code == 0, f"statement probe failed for {case_id}:{label}")
                    type_outputs.append(type_result.stdout + type_result.stderr)
                    type_results.append((label, type_result))
                statement_preserved = type_outputs[0] == type_outputs[1]
                require(statement_preserved, f"declaration type changed in repair {case_id}")
                observed_warnings = warning_lines(linter_result.stdout + linter_result.stderr)
            whitelist = spec.get("warning_whitelist", [])
            for required_warning in spec.get("required_warning_substrings", []):
                require(any(required_warning in warning for warning in observed_warnings),
                        f"required warning missing for {case_id}: {required_warning}")
            for required_warning in spec.get("required_baseline_warning_substrings", []):
                require(any(required_warning in warning for warning in baseline_warnings),
                        f"required baseline warning missing for {case_id}: {required_warning}")
            unexpected = [
                warning for warning in observed_warnings
                if not any(allowed in warning for allowed in whitelist)
            ]
            if spec:
                require(not unexpected, f"unexpected warnings for {case_id}: {unexpected}")
            if load_json(public_path)["task"] == "REPAIR" and write_records:
                require(after_relative is not None, f"repair case lacks executable reference: {case_id}")
            if write_records:
                log_artifacts = {
                    "compile.stdout": result.raw_stdout,
                    "compile.stderr": result.raw_stderr,
                    "checker.stdout": checker.raw_stdout,
                    "checker.stderr": checker.raw_stderr,
                    "standard-linter.stdout": linter_result.raw_stdout,
                    "standard-linter.stderr": linter_result.raw_stderr,
                    "text-linter.stdout": text_linter_result.raw_stdout,
                    "text-linter.stderr": text_linter_result.raw_stderr,
                    "axiom-probe.stdout": after_probe_result.raw_stdout if after_relative
                        else probe_result.raw_stdout,
                    "axiom-probe.stderr": after_probe_result.raw_stderr if after_relative
                        else probe_result.raw_stderr,
                }
                if location_probe_result is not None:
                    log_artifacts.update({
                        "find-home.stdout": location_probe_result.raw_stdout,
                        "find-home.stderr": location_probe_result.raw_stderr,
                    })
                if after_relative:
                    log_artifacts.update({
                        "baseline-compile.stdout": baseline_result.raw_stdout,
                        "baseline-compile.stderr": baseline_result.raw_stderr,
                        "baseline-checker.stdout": baseline_checker.raw_stdout,
                        "baseline-checker.stderr": baseline_checker.raw_stderr,
                        "baseline-standard-linter.stdout": baseline_linter_result.raw_stdout,
                        "baseline-standard-linter.stderr": baseline_linter_result.raw_stderr,
                        "baseline-text-linter.stdout": baseline_text_linter_result.raw_stdout,
                        "baseline-text-linter.stderr": baseline_text_linter_result.raw_stderr,
                        "baseline-axiom-probe.stdout": baseline_probe_result.raw_stdout,
                        "baseline-axiom-probe.stderr": baseline_probe_result.raw_stderr,
                    })
                    for label, type_result in type_results:
                        log_artifacts[f"statement-{label}.stdout"] = type_result.raw_stdout
                        log_artifacts[f"statement-{label}.stderr"] = type_result.raw_stderr
                record_path = write_validation_record(
                    private_root, case_id, result, checker, baseline_axioms, observed_axioms,
                    observed_warnings, baseline_warnings,
                    whitelist, sha256_file(validated_source),
                    sha256_bytes(result.raw_stdout.encode()),
                    sha256_bytes(result.raw_stderr.encode()), statement_preserved,
                    spec.get("validator_ids", []), log_artifacts,
                )
                validate_document(record_path, validators["validation-record.schema.json"])
            compiled += 1
    return compiled


def check_public_hash_manifest() -> int:
    path = ROOT / "manifests" / "PUBLIC_SHA256.json"
    if not path.is_file():
        return 0
    manifest = load_json(path)
    for relative, expected in manifest["files"].items():
        candidate = ROOT / relative
        require(candidate.is_file(), f"public hash target missing: {relative}")
        require(sha256_file(candidate) == expected, f"public hash drift: {relative}")
    return len(manifest["files"])


def refresh_public_hash_manifest() -> Path:
    files: dict[str, str] = {}
    for path in sorted((ROOT / "cases").glob("*/*/**/*")):
        if path.is_file():
            files[str(path.relative_to(ROOT))] = sha256_file(path)
    pilot = ROOT / "manifests" / "PILOT_CASES.json"
    files[str(pilot.relative_to(ROOT))] = sha256_file(pilot)
    target = ROOT / "manifests" / "PUBLIC_SHA256.json"
    target.write_text(
        json.dumps(
            {
                "manifest_version": "1.0.0",
                "hash_algorithm": "sha256",
                "scope": (
                    "Phase 4 public case asset freeze; case asset bytes were frozen "
                    "before blind annotation"
                ),
                "files": dict(sorted(files.items())),
            },
            ensure_ascii=False,
            indent=2,
        ) + "\n",
        encoding="utf-8",
    )
    return target


def refresh_private_hash_manifest(private_root: Path) -> Path:
    target = private_root / "release_manifests" / "PRIVATE_SHA256.json"
    files: dict[str, str] = {}
    for path in sorted(private_root.rglob("*")):
        if path.is_file() and path != target:
            files[str(path.relative_to(private_root))] = sha256_file(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(
        json.dumps(
            {
                "manifest_version": "1.0.0",
                "hash_algorithm": "sha256",
                "custody": "ignored-local-private",
                "environment_ref": "MATHLIB-4.30.0",
                "mathlib_commit": EXPECTED_MATHLIB_COMMIT,
                "lean_toolchain": "leanprover/lean4:v4.30.0",
                "host_platform": platform.platform(),
                "public_manifest_sha256": sha256_file(
                    ROOT / "manifests" / "PUBLIC_SHA256.json"
                ),
                "files": dict(sorted(files.items())),
            },
            ensure_ascii=False,
            indent=2,
        ) + "\n",
        encoding="utf-8",
    )
    return target


def check_private_hash_manifest(private_root: Path) -> int:
    target = private_root / "release_manifests" / "PRIVATE_SHA256.json"
    require(target.is_file(), "private custody hash manifest is missing")
    manifest = load_json(target)
    require(manifest.get("hash_algorithm") == "sha256",
            "private custody hash algorithm drift")
    require(manifest.get("public_manifest_sha256") == sha256_file(
        ROOT / "manifests" / "PUBLIC_SHA256.json"
    ), "private custody public-manifest link drift")
    expected_files = {
        str(path.relative_to(private_root))
        for path in private_root.rglob("*")
        if path.is_file() and path != target
    }
    require(set(manifest.get("files", {})) == expected_files,
            "private custody manifest inventory drift")
    for relative, expected in manifest["files"].items():
        require(sha256_file(private_root / relative) == expected,
                f"private custody hash drift: {relative}")
    return len(expected_files)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--private-root", type=Path, default=PRIVATE_DEFAULT)
    parser.add_argument("--timeout", type=int, default=90)
    parser.add_argument("--write-records", action="store_true")
    parser.add_argument("--public-only", action="store_true")
    parser.add_argument("--refresh-public-hashes", action="store_true")
    parser.add_argument("--refresh-private-hashes", action="store_true")
    args = parser.parse_args()
    try:
        validators = schema_validators()
        manifest, documents = validate_public_layout(validators)
        scan_public_leakage()
        private_count = 0 if args.public_only else validate_private(validators, args.private_root)
        if not args.public_only:
            provenance = subprocess.run(
                [
                    sys.executable,
                    str(ROOT / "scripts" / "check_phase4_provenance.py"),
                    "--private-root",
                    str(args.private_root),
                ],
                cwd=REPO_ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            require(
                provenance.returncode == 0,
                "private provenance audit failed:\n" + provenance.stdout + provenance.stderr,
            )
            annotation_isolation = subprocess.run(
                [sys.executable, str(ROOT / "scripts" / "check_annotation_isolation.py")],
                cwd=REPO_ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            require(
                annotation_isolation.returncode == 0,
                "annotation-isolation audit failed:\n"
                + annotation_isolation.stdout
                + annotation_isolation.stderr,
            )
        if args.refresh_public_hashes:
            refresh_public_hash_manifest()
        hash_count = check_public_hash_manifest()
        compile_private_root = (
            ROOT / "heldout" / ".public-only-private-disabled"
            if args.public_only
            else args.private_root
        )
        compile_count = compile_cases(
            manifest, validators, compile_private_root, args.timeout, args.write_records
        )
        private_hash_count = 0
        if not args.public_only:
            if args.write_records or args.refresh_private_hashes:
                refresh_private_hash_manifest(args.private_root)
            private_hash_count = check_private_hash_manifest(args.private_root)
        print(
            "phase4 hard gates passed: "
            f"{len(manifest['primary_case_ids'])} primary + {len(manifest['pair_mirrors'])} mirrors; "
            f"{compile_count} compiled twice; {private_count} private JSON; "
            f"{hash_count} public hashes; {private_hash_count} private hashes"
        )
        return 0
    except HarnessFailure as exc:
        print(f"phase4 hard gate failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
