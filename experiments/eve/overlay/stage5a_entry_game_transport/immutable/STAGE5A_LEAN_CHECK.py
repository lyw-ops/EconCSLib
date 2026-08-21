#!/usr/bin/env python3
"""Run the real local Lean check and record a compact, auditable event."""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path


WORKSPACE = Path(__file__).resolve().parent
CANDIDATE = WORKSPACE / "solver" / "Candidate.lean"
EVENTS = WORKSPACE / ".scaling_evolve" / "stage5a-lean-checks.jsonl"


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def main() -> int:
    repo_value = os.environ.get("EVE_ECONCSLIB_ROOT")
    if not repo_value:
        print("EVE_ECONCSLIB_ROOT is unavailable", file=sys.stderr)
        return 2
    repo_root = Path(repo_value).resolve()
    if not CANDIDATE.is_file() or not (repo_root / "lakefile.toml").is_file():
        print("Candidate or EconCSLib Lake root is unavailable", file=sys.stderr)
        return 2
    command = ["lake", "env", "lean", str(CANDIDATE)]
    completed = subprocess.run(
        command,
        cwd=repo_root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    stdout = completed.stdout.encode("utf-8")
    stderr = completed.stderr.encode("utf-8")
    event = {
        "schema_version": "1.0.0",
        "observed_at": dt.datetime.now(dt.UTC).isoformat(),
        "command": ["lake", "env", "lean", "solver/Candidate.lean"],
        "candidate_sha256": sha256_bytes(CANDIDATE.read_bytes()),
        "exit_code": completed.returncode,
        "failed": completed.returncode != 0,
        "stdout_sha256": sha256_bytes(stdout),
        "stderr_sha256": sha256_bytes(stderr),
        "stdout_bytes": len(stdout),
        "stderr_bytes": len(stderr),
    }
    EVENTS.parent.mkdir(parents=True, exist_ok=True)
    with EVENTS.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(event, sort_keys=True) + "\n")
    if completed.stdout:
        print(completed.stdout, end="")
    if completed.stderr:
        print(completed.stderr, end="", file=sys.stderr)
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
