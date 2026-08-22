#!/usr/bin/env python3
"""Zero-model terminal Lean-check contract for Stage 5B Sol REP-002."""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any


EXPECTED_PYTHON_VERSION = "3.9.6"
EXPECTED_PYTHON_INVOCATION = "/usr/bin/python3"
EXPECTED_PYTHON_EXECUTABLE = "/Library/Developer/CommandLineTools/usr/bin/python3"
EXPECTED_CHECK_COMMAND = ["lake", "env", "lean", "solver/Candidate.lean"]
_HEX64 = re.compile(r"[0-9a-f]{64}")


class TerminalCheckError(RuntimeError):
    """The wrapper could not establish final-candidate checker evidence."""


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def event_sha256(event: dict[str, object]) -> str:
    payload = {key: value for key, value in event.items() if key != "event_sha256"}
    encoded = json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and _HEX64.fullmatch(value) is not None


def _evidence_path(workspace: Path) -> Path:
    return workspace / ".scaling_evolve" / "stage5a-lean-checks.jsonl"


def _nonempty_line_count(path: Path) -> int:
    if not path.is_file():
        return 0
    return sum(bool(line.strip()) for line in path.read_text(encoding="utf-8").splitlines())


def load_events(workspace: Path) -> list[dict[str, Any]]:
    path = _evidence_path(workspace)
    if not path.is_file():
        raise TerminalCheckError("required Sol REP-002 Lean-check evidence is missing")
    lines = [line for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
    if not lines:
        raise TerminalCheckError("required Sol REP-002 Lean-check evidence is empty")
    events: list[dict[str, Any]] = []
    for line in lines:
        try:
            value = json.loads(line)
        except json.JSONDecodeError as exc:
            raise TerminalCheckError("Sol REP-002 Lean-check evidence is malformed") from exc
        if not isinstance(value, dict):
            raise TerminalCheckError("Sol REP-002 Lean-check event is not an object")
        events.append(value)
    return events


def validate_events(
    events: list[dict[str, Any]],
    *,
    checker_sha256: str,
    final_candidate_sha256: str,
) -> None:
    """Validate the entire immutable-checker chain and its final candidate join."""
    if not events:
        raise TerminalCheckError("required Sol REP-002 Lean-check evidence is empty")
    previous: str | None = None
    for sequence, event in enumerate(events, start=1):
        if event.get("schema_version") != "2.0.0":
            raise TerminalCheckError("Sol REP-002 Lean-check schema is invalid")
        if event.get("sequence") != sequence:
            raise TerminalCheckError("Sol REP-002 Lean-check sequence is not contiguous")
        if event.get("previous_event_sha256") != previous:
            raise TerminalCheckError("Sol REP-002 Lean-check hash chain is invalid")
        if event.get("checker_sha256") != checker_sha256:
            raise TerminalCheckError("Sol REP-002 Lean check used a different checker")
        if event.get("event_sha256") != event_sha256(event):
            raise TerminalCheckError("Sol REP-002 Lean-check event hash is invalid")
        for key in (
            "candidate_sha256",
            "guidance_sha256",
            "stdout_sha256",
            "stderr_sha256",
            "event_sha256",
        ):
            if not _is_hash(event.get(key)):
                raise TerminalCheckError(f"Sol REP-002 Lean-check {key} is invalid")
        if event.get("python_invocation") != EXPECTED_PYTHON_INVOCATION:
            raise TerminalCheckError("Sol REP-002 checker invocation drifted")
        if event.get("python_executable") != EXPECTED_PYTHON_EXECUTABLE:
            raise TerminalCheckError("Sol REP-002 checker executable drifted")
        if event.get("python_version") != EXPECTED_PYTHON_VERSION:
            raise TerminalCheckError("Sol REP-002 checker Python version drifted")
        if event.get("command") != EXPECTED_CHECK_COMMAND:
            raise TerminalCheckError("Sol REP-002 Lean command drifted")
        exit_code = event.get("exit_code")
        failed = event.get("failed")
        if isinstance(exit_code, bool) or not isinstance(exit_code, int):
            raise TerminalCheckError("Sol REP-002 Lean-check exit status is invalid")
        if not isinstance(failed, bool) or failed != (exit_code != 0):
            raise TerminalCheckError("Sol REP-002 Lean-check failure flag is inconsistent")
        for key in ("stdout_bytes", "stderr_bytes"):
            value = event.get(key)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise TerminalCheckError(f"Sol REP-002 Lean-check {key} is invalid")
        try:
            instant = dt.datetime.fromisoformat(str(event.get("observed_at")))
        except ValueError as exc:
            raise TerminalCheckError("Sol REP-002 Lean-check timestamp is malformed") from exc
        if instant.utcoffset() != dt.timedelta(0):
            raise TerminalCheckError("Sol REP-002 Lean-check timestamp is not UTC")
        previous = str(event["event_sha256"])
    if events[-1].get("candidate_sha256") != final_candidate_sha256:
        raise TerminalCheckError(
            "Sol REP-002 final checker event does not match final candidate"
        )


def run_terminal_checker(
    workspace: Path,
    *,
    expected_checker_sha256: str,
) -> dict[str, Any]:
    """Append and validate one wrapper-owned post-agent, pre-evaluation check."""
    workspace = workspace.resolve()
    candidate = workspace / "solver" / "Candidate.lean"
    checker = workspace / "STAGE5A_LEAN_CHECK.py"
    if not candidate.is_file():
        raise TerminalCheckError("Sol REP-002 final candidate is missing")
    if not checker.is_file():
        raise TerminalCheckError("Sol REP-002 immutable Lean checker is missing")
    checker_hash = file_sha256(checker)
    if checker_hash != expected_checker_sha256:
        raise TerminalCheckError("Sol REP-002 immutable Lean checker changed during rollout")

    evidence_path = _evidence_path(workspace)
    prior_count = _nonempty_line_count(evidence_path)
    candidate_before = file_sha256(candidate)
    completed = subprocess.run(
        [EXPECTED_PYTHON_INVOCATION, str(checker)],
        cwd=workspace,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    candidate_after = file_sha256(candidate)
    if candidate_after != candidate_before:
        raise TerminalCheckError("Sol REP-002 checker changed the final candidate")

    events = load_events(workspace)
    if len(events) != prior_count + 1:
        raise TerminalCheckError(
            "Sol REP-002 terminal checker did not append exactly one evidence event"
        )
    validate_events(
        events,
        checker_sha256=checker_hash,
        final_candidate_sha256=candidate_after,
    )
    final_event = events[-1]
    if final_event.get("exit_code") != completed.returncode:
        raise TerminalCheckError("Sol REP-002 terminal checker exit status drifted")
    for key, observed in (
        ("stdout_sha256", hashlib.sha256(completed.stdout).hexdigest()),
        ("stderr_sha256", hashlib.sha256(completed.stderr).hexdigest()),
        ("stdout_bytes", len(completed.stdout)),
        ("stderr_bytes", len(completed.stderr)),
    ):
        if final_event.get(key) != observed:
            raise TerminalCheckError(f"Sol REP-002 terminal checker {key} drifted")
    return {
        "terminal_checker_phase": "post-agent-pre-evaluation",
        "terminal_checker_invocation": EXPECTED_PYTHON_INVOCATION,
        "terminal_checker_exit_code": completed.returncode,
        "terminal_check_event_sha256": final_event["event_sha256"],
        "terminal_check_sequence": final_event["sequence"],
        "terminal_check_count": len(events),
        "final_candidate_sha256": candidate_after,
        "lean_checker_sha256": checker_hash,
        "local_lean_checks": events,
    }
