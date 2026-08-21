#!/usr/bin/env python3
"""Shared deterministic safety helpers for public EconCSLib EvE evaluators."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


TRUST_BYPASS_PATTERN = re.compile(
    r"(?m)(?:^|\s)(unsafe|opaque|extern|run_tac|#eval)(?:\s|$)|implemented_by"
)
AXIOM_OUTPUT_PATTERN = re.compile(r"depends on axioms:\s*\[([^\]]*)\]", re.S)
IMPORT_PATTERN = re.compile(r"(?m)^\s*import\s+([^\r\n]+)$")


@dataclass(frozen=True)
class CommandResult:
    """Captured result of a deterministic local command."""

    returncode: int
    output: str


def sha256(path: Path) -> str:
    """Return the hexadecimal SHA-256 digest of one file."""

    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(65536):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    """Load a JSON object, rejecting non-object roots."""

    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"Expected a JSON object: {path.name}")
    return payload


def is_relative_to(path: Path, parent: Path) -> bool:
    """Compatibility spelling for a containment check."""

    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def safe_directory(path: Path, *, label: str, repository_root: Path) -> Path:
    """Resolve one narrow existing directory and reject dangerous roots."""

    resolved = path.expanduser().resolve()
    forbidden = {
        Path("/").resolve(),
        Path.home().resolve(),
        repository_root.resolve(),
    }
    if resolved in forbidden:
        raise ValueError(f"{label} is too broad")
    if not resolved.is_dir():
        raise ValueError(f"{label} is not a directory")
    return resolved


def tree_files(root: Path) -> dict[str, Path]:
    """Enumerate regular files below a candidate root and reject symlinks."""

    files: dict[str, Path] = {}
    for path in sorted(root.rglob("*")):
        if path.is_symlink():
            raise ValueError(f"symlink is not allowed: {path.relative_to(root)}")
        if path.is_file():
            files[path.relative_to(root).as_posix()] = path
    return files


def boundary_failures(
    baseline: Path, candidate: Path, *, editable_file: str
) -> list[str]:
    """Compare complete trees while allowing exactly one file to differ."""

    baseline_files = tree_files(baseline)
    candidate_files = tree_files(candidate)
    failures: list[str] = []
    if editable_file not in candidate_files:
        failures.append("editable-file-missing")
    for path in sorted(candidate_files.keys() - baseline_files.keys()):
        failures.append(f"forbidden-created:{path}")
    for path in sorted(baseline_files.keys() - candidate_files.keys()):
        failures.append(f"forbidden-deleted:{path}")
    for path in sorted(baseline_files.keys() & candidate_files.keys()):
        if path != editable_file and sha256(baseline_files[path]) != sha256(
            candidate_files[path]
        ):
            failures.append(f"forbidden-modified:{path}")
    return failures


def load_guard_module(static_guard: Path, *, module_name: str) -> Any:
    """Load the repository's audited static Lean guard."""

    spec = importlib.util.spec_from_file_location(module_name, static_guard)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load the repository static guard")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run(
    command: list[str],
    *,
    cwd: Path,
    timeout: int,
) -> CommandResult:
    """Run a local deterministic command with captured output and a timeout."""

    try:
        completed = subprocess.run(
            command,
            cwd=cwd,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
            timeout=timeout,
            env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
        )
    except subprocess.TimeoutExpired:
        return CommandResult(returncode=124, output="command timed out")
    return CommandResult(completed.returncode, completed.stdout)


def normalize_output(text: str, temporary_root: Path, repository_root: Path) -> str:
    """Remove evaluator-local absolute paths from diagnostics."""

    normalized = text.replace(str(temporary_root), "<temporary>")
    normalized = normalized.replace(str(repository_root), "<repo>")
    return "\n".join(line.rstrip() for line in normalized.splitlines()).strip()


def protected_hashes(paths: Iterable[Path]) -> dict[str, str]:
    """Snapshot protected evaluator assets by resolved path."""

    return {str(path.resolve()): sha256(path.resolve()) for path in paths}


def source_imports(clean_source: str) -> list[str]:
    """Return every whitespace-separated module named by an import command."""

    imports: list[str] = []
    for match in IMPORT_PATTERN.finditer(clean_source):
        imports.extend(match.group(1).split())
    return imports


def axioms(output: str) -> list[str]:
    """Extract all axioms reported by Lean's `#print axioms` output."""

    found: set[str] = set()
    for match in AXIOM_OUTPUT_PATTERN.finditer(output):
        found.update(item.strip() for item in match.group(1).split(",") if item.strip())
    return sorted(found)


def write_score(path: Path, report: dict[str, Any]) -> None:
    """Write the exact two-field EvE v0.2.0 score PyTree."""

    resolved = path.expanduser().resolve()
    resolved.parent.mkdir(parents=True, exist_ok=True)
    summary = json.dumps(str(report["summary"]), ensure_ascii=True)
    resolved.write_text(
        f"score: {float(report['score']):.1f}\nsummary: {summary}\n",
        encoding="utf-8",
    )


def write_report(path: Path, report: dict[str, Any]) -> None:
    """Write the detailed deterministic JSON report outside the solver tree."""

    resolved = path.expanduser().resolve()
    resolved.parent.mkdir(parents=True, exist_ok=True)
    resolved.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
