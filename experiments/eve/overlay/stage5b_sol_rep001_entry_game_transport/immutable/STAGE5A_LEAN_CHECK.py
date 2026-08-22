#!/usr/bin/env python3
"""Run Lean and record fail-closed DEV-003 checker evidence."""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import os
import platform
import subprocess
import sys
from pathlib import Path


WORKSPACE = Path(__file__).resolve().parent
CANDIDATE = WORKSPACE / "solver" / "Candidate.lean"
GUIDANCE = WORKSPACE / "guidance"
EVENTS = WORKSPACE / ".scaling_evolve" / "stage5a-lean-checks.jsonl"
EXPECTED_PYTHON_VERSION = "3.9.6"
EXPECTED_PYTHON_INVOCATION = "/usr/bin/python3"
EXPECTED_PYTHON_EXECUTABLE = "/Library/Developer/CommandLineTools/usr/bin/python3"


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def tree_sha256(root: Path) -> str:
    digest = hashlib.sha256()
    if not root.is_dir():
        return digest.hexdigest()
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        relative = path.relative_to(root).as_posix().encode("utf-8")
        content = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return digest.hexdigest()


def event_sha256(event: dict[str, object]) -> str:
    payload = {key: value for key, value in event.items() if key != "event_sha256"}
    encoded = json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return sha256_bytes(encoded)


def next_sequence() -> tuple[int, str | None]:
    if not EVENTS.is_file():
        return 1, None
    previous: str | None = None
    lines = [line for line in EVENTS.read_text(encoding="utf-8").splitlines() if line]
    if not lines:
        raise RuntimeError("existing DEV-003 Lean-check evidence is empty")
    for sequence, line in enumerate(lines, start=1):
        event = json.loads(line)
        if (
            not isinstance(event, dict)
            or event.get("sequence") != sequence
            or event.get("previous_event_sha256") != previous
            or event.get("event_sha256") != event_sha256(event)
        ):
            raise RuntimeError("existing DEV-003 Lean-check chain is invalid")
        previous = str(event["event_sha256"])
    return len(lines) + 1, previous


def main() -> int:
    if platform.python_version() != EXPECTED_PYTHON_VERSION:
        print(
            "DEV-003 checker requires exact isolated solver Python 3.9.6",
            file=sys.stderr,
        )
        return 2
    if sys.executable != EXPECTED_PYTHON_EXECUTABLE:
        print("DEV-003 checker Python executable identity drifted", file=sys.stderr)
        return 2
    repo_value = os.environ.get("EVE_ECONCSLIB_ROOT")
    if not repo_value:
        print("EVE_ECONCSLIB_ROOT is unavailable", file=sys.stderr)
        return 2
    repo_root = Path(repo_value).resolve()
    if not CANDIDATE.is_file() or not (repo_root / "lakefile.toml").is_file():
        print("Candidate or EconCSLib Lake root is unavailable", file=sys.stderr)
        return 2
    try:
        sequence, previous_event_sha256 = next_sequence()
    except (OSError, ValueError, json.JSONDecodeError, RuntimeError) as exc:
        print(str(exc), file=sys.stderr)
        return 2
    command = ["lake", "env", "lean", str(CANDIDATE)]
    completed = subprocess.run(
        command,
        cwd=repo_root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    stdout = completed.stdout
    stderr = completed.stderr
    event = {
        "schema_version": "2.0.0",
        "sequence": sequence,
        "previous_event_sha256": previous_event_sha256,
        "observed_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "python_invocation": EXPECTED_PYTHON_INVOCATION,
        "python_executable": sys.executable,
        "python_version": platform.python_version(),
        "command": ["lake", "env", "lean", "solver/Candidate.lean"],
        "checker_sha256": sha256_bytes(Path(__file__).read_bytes()),
        "candidate_sha256": sha256_bytes(CANDIDATE.read_bytes()),
        "guidance_sha256": tree_sha256(GUIDANCE),
        "exit_code": completed.returncode,
        "failed": completed.returncode != 0,
        "stdout_sha256": sha256_bytes(stdout),
        "stderr_sha256": sha256_bytes(stderr),
        "stdout_bytes": len(stdout),
        "stderr_bytes": len(stderr),
    }
    event["event_sha256"] = event_sha256(event)
    EVENTS.parent.mkdir(parents=True, exist_ok=True)
    with EVENTS.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(event, sort_keys=True) + "\n")
    if stdout:
        sys.stdout.buffer.write(stdout)
    if stderr:
        sys.stderr.buffer.write(stderr)
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
