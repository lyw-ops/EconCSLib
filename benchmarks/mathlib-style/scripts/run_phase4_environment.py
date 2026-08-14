#!/usr/bin/env python3
"""Run Phase 4 gates and emit auditable environment evidence.

The evidence record is deliberately separate from the frozen v0.3.0 benchmark
schemas. It records the execution environment around those schema-governed
case validation records and never changes their contract.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

from phase4_harness import refresh_private_hash_manifest


ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = ROOT.parents[1]
PRIVATE_ROOT = ROOT / "heldout" / "private"
EXPECTED_MATHLIB_COMMIT = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
EXPECTED_LEAN = "version 4.30.0"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(command: list[str], timeout: int) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
        timeout=timeout,
    )


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--label", required=True)
    parser.add_argument("--output-root", type=Path, default=PRIVATE_ROOT / "environments")
    parser.add_argument("--timeout", type=int, default=90)
    parser.add_argument("--public-only", action="store_true")
    args = parser.parse_args()

    output_dir = args.output_root / args.label
    output_dir.mkdir(parents=True, exist_ok=True)

    lean = run(["lake", "env", "lean", "--version"], args.timeout)
    mathlib = run(
        [
            "git",
            "-C",
            str(REPO_ROOT / ".lake" / "packages" / "mathlib"),
            "rev-parse",
            "HEAD",
        ],
        args.timeout,
    )
    identity_text = (
        "$ lake env lean --version\n"
        + lean.stdout
        + lean.stderr
        + "$ git -C .lake/packages/mathlib rev-parse HEAD\n"
        + mathlib.stdout
        + mathlib.stderr
    )
    (output_dir / "identity.log").write_text(identity_text, encoding="utf-8")

    identity_ok = (
        lean.returncode == 0
        and EXPECTED_LEAN in lean.stdout
        and mathlib.returncode == 0
        and mathlib.stdout.strip() == EXPECTED_MATHLIB_COMMIT
    )
    harness_command = [
        sys.executable,
        str(ROOT / "scripts" / "phase4_harness.py"),
        "--timeout",
        str(args.timeout),
    ]
    if args.public_only:
        harness_command.append("--public-only")
    else:
        harness_command.append("--write-records")

    started_at = utc_now()
    started = time.monotonic()
    if identity_ok:
        harness = run(harness_command, max(args.timeout * 160, 1800))
    else:
        harness = subprocess.CompletedProcess(harness_command, 125, "", "identity gate failed\n")
    duration_ms = round((time.monotonic() - started) * 1000)
    finished_at = utc_now()
    stdout_bytes = harness.stdout.encode()
    stderr_bytes = harness.stderr.encode()
    (output_dir / "harness.stdout").write_bytes(stdout_bytes)
    (output_dir / "harness.stderr").write_bytes(stderr_bytes)

    public_manifest = ROOT / "manifests" / "PUBLIC_SHA256.json"
    uname = platform.uname()
    record = {
        "environment_record_version": "1.0.0",
        "label": args.label,
        "status": "PASSED" if identity_ok and harness.returncode == 0 else "FAILED",
        "validation_mode": "PUBLIC_ONLY" if args.public_only else "FULL_PRIVATE_CUSTODY",
        "started_at": started_at,
        "finished_at": finished_at,
        "duration_ms": duration_ms,
        "os": uname.system,
        "os_release": uname.release,
        "architecture": uname.machine,
        "platform": platform.platform(),
        "python_version": platform.python_version(),
        "lean_version": (lean.stdout + lean.stderr).strip(),
        "lean_identity_exit_code": lean.returncode,
        "mathlib_commit": mathlib.stdout.strip(),
        "expected_mathlib_commit": EXPECTED_MATHLIB_COMMIT,
        "mathlib_identity_exit_code": mathlib.returncode,
        "identity_gate_passed": identity_ok,
        "command": harness_command,
        "timeout_seconds_per_case": args.timeout,
        "exit_code": harness.returncode,
        "logs": {
            "identity": {
                "path": "identity.log",
                "sha256": sha256(identity_text.encode()),
            },
            "stdout": {"path": "harness.stdout", "sha256": sha256(stdout_bytes)},
            "stderr": {"path": "harness.stderr", "sha256": sha256(stderr_bytes)},
        },
        "public_manifest_sha256": sha256(public_manifest.read_bytes()),
    }
    (output_dir / "environment.json").write_text(
        json.dumps(record, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    if not args.public_only:
        refresh_private_hash_manifest(PRIVATE_ROOT)
    print(json.dumps(record, ensure_ascii=False, indent=2))
    return 0 if record["status"] == "PASSED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
