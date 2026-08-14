#!/usr/bin/env python3
"""Run frozen fixture regression checks and the Phase 4 benchmark hard gates."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def find_lake_root() -> Path | None:
    for candidate in (ROOT, *ROOT.parents):
        if (candidate / "lakefile.toml").is_file() or (candidate / "lakefile.lean").is_file():
            return candidate
    return None


def run(command: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=cwd, text=True, capture_output=True, check=False)


def main() -> int:
    structural = run([sys.executable, str(ROOT / "scripts" / "check_distillation.py")], ROOT)
    if structural.returncode != 0:
        sys.stderr.write(structural.stdout)
        sys.stderr.write(structural.stderr)
        return structural.returncode

    preservation = run(
        [sys.executable, str(ROOT / "scripts" / "check_phase4_preservation.py")], ROOT
    )
    if preservation.returncode != 0:
        sys.stderr.write(preservation.stdout)
        sys.stderr.write(preservation.stderr)
        return preservation.returncode

    lake_root = find_lake_root()
    if lake_root is None:
        print("benchmark check failed: no parent Lake project found", file=sys.stderr)
        return 1

    version = run(["lake", "env", "lean", "--version"], lake_root)
    if version.returncode != 0 or "version 4.30.0" not in version.stdout:
        print(
            "benchmark check failed: expected Lean 4.30.0, got "
            + (version.stdout + version.stderr).strip(),
            file=sys.stderr,
        )
        return 1

    manifests = []
    for kind in ("positive", "negative", "repair"):
        manifests.extend(sorted((ROOT / "fixtures" / kind).glob("*/case.json")))

    compiled = 0
    with tempfile.TemporaryDirectory(prefix="mathlib-style-bench-") as temp:
        output_dir = Path(temp)
        for manifest_path in manifests:
            case = json.loads(manifest_path.read_text(encoding="utf-8"))
            warning_files = set(case["expected_warning_files"])
            for index, relative in enumerate(case["compile_files"]):
                source = (manifest_path.parent / relative).resolve()
                output = output_dir / f"{case['id']}-{index}.olean"
                result = run(
                    ["lake", "env", "lean", "-o", str(output), str(source)],
                    lake_root,
                )
                combined = result.stdout + result.stderr
                if result.returncode != 0:
                    print(
                        f"benchmark check failed: {case['id']}:{relative} did not compile\n{combined}",
                        file=sys.stderr,
                    )
                    return 1
                has_warning = "warning:" in combined.lower()
                if relative in warning_files and not has_warning:
                    print(
                        f"benchmark check failed: {case['id']}:{relative} "
                        "did not emit its expected target warning",
                        file=sys.stderr,
                    )
                    return 1
                if relative not in warning_files and has_warning:
                    print(
                        f"benchmark check failed: {case['id']}:{relative} "
                        f"emitted an unexpected warning\n{combined}",
                        file=sys.stderr,
                    )
                    return 1
                compiled += 1

    phase4 = run(
        [
            sys.executable,
            str(ROOT / "scripts" / "phase4_harness.py"),
            "--public-only",
        ],
        lake_root,
    )
    if phase4.returncode != 0:
        sys.stderr.write(phase4.stdout)
        sys.stderr.write(phase4.stderr)
        return phase4.returncode

    print(
        f"benchmark check passed: {len(manifests)} frozen fixture cases, "
        f"{compiled} fixture Lean files, Lean 4.30.0"
    )
    print(phase4.stdout.strip())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
