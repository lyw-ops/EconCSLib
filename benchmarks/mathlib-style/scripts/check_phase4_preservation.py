#!/usr/bin/env python3
"""Verify Phase 4 preserved the captured pre-Phase-4 artifact surface."""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
BASELINE = Path(__file__).resolve().parents[1] / "reports" / "phase4" / "BASELINE_SHA256.json"
EXPECTED_BASELINE_EDITS = {
    "AGENTS.md",
    "benchmarks/mathlib-style/AGENTS.md",
    "benchmarks/mathlib-style/README.md",
    "benchmarks/mathlib-style/manifests/COVERAGE.json",
    "benchmarks/mathlib-style/manifests/RULES.json",
    "benchmarks/mathlib-style/manifests/SOURCES.json",
    "benchmarks/mathlib-style/manifests/VALIDATORS.json",
    "benchmarks/mathlib-style/scripts/check_benchmark.py",
    "benchmarks/mathlib-style/scripts/check_distillation.py",
    "benchmarks/mathlib-style/scripts/static_lean_guard.py",
    "docs/research/mathlib-style/DECISIONS.md",
    "docs/research/mathlib-style/README.md",
    "docs/research/mathlib-style/VERSION.md",
}

EXPECTED_ENGLISH_ONLY_REMOVALS = {
    "docs/research/mathlib-style/MANUAL_ZH.md",
    "docs/research/mathlib-style/PHASE1_COMPLETION_REPORT_ZH.md",
    "docs/research/mathlib-style/PHASE3_COMPLETION_REPORT_ZH.md",
    "docs/research/mathlib-style/REPOSITORY_INTEGRATION_ZH.md",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))
    missing: list[str] = []
    unexpected: list[str] = []
    expected: list[str] = []
    removed: list[str] = []
    unchanged = 0
    for entry in baseline["files"]:
        relative, old_hash = entry["path"], entry["sha256"]
        path = REPO_ROOT / relative
        if not path.is_file():
            if relative in EXPECTED_ENGLISH_ONLY_REMOVALS:
                removed.append(relative)
            else:
                missing.append(relative)
            continue
        new_hash = sha256(path)
        if new_hash == old_hash:
            unchanged += 1
        elif relative in EXPECTED_BASELINE_EDITS:
            expected.append(relative)
        else:
            unexpected.append(relative)
    if (
        missing
        or unexpected
        or set(expected) != EXPECTED_BASELINE_EDITS
        or set(removed) != EXPECTED_ENGLISH_ONLY_REMOVALS
    ):
        print(
            json.dumps(
                {
                    "status": "failed",
                    "missing": missing,
                    "unexpected_changes": unexpected,
                    "expected_changes_observed": expected,
                    "expected_removals_observed": removed,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    print(
        f"phase4 preservation passed: {unchanged} captured files unchanged; "
        f"{len(expected)} expected integration files changed; "
        f"{len(removed)} translated files removed by the English-only migration"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
