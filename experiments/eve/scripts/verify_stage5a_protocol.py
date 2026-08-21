#!/usr/bin/env python3
"""Verify the detached Stage 5A protocol hash and every frozen input."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


RUNNER_PATH = Path(__file__).resolve().with_name("run_stage5a.py")


def _load_runner():
    spec = importlib.util.spec_from_file_location("stage5a_protocol_runner", RUNNER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load {RUNNER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules["stage5a_protocol_runner"] = module
    spec.loader.exec_module(module)
    return module


def main() -> int:
    runner = _load_runner()
    try:
        protocol = runner.verify_protocol_assets()
    except (runner.CheckError, OSError, ValueError) as exc:
        print(f"Stage 5A protocol verification failed: {exc}")
        return 2
    print(
        f"Stage 5A protocol verified: {protocol['id']} "
        f"{protocol['version']} {protocol['status']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
