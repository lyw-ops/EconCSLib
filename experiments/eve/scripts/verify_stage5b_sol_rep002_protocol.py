#!/usr/bin/env python3
"""Verify the detached Sol REP-002 protocol, frozen assets, and committed Lean tree."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path


RUNNER_PATH = Path(__file__).resolve().with_name("run_stage5b_sol_rep002.py")


def _load_runner():
    spec = importlib.util.spec_from_file_location("stage5b_sol_rep002_protocol_runner", RUNNER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load {RUNNER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules["stage5b_sol_rep002_protocol_runner"] = module
    spec.loader.exec_module(module)
    return module


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-checkout", type=Path)
    args = parser.parse_args(argv)
    runner = _load_runner()
    try:
        protocol = runner.verify_protocol_assets(args.lean_checkout)
    except (runner.CheckError, OSError, ValueError) as exc:
        print(f"Stage 5B Sol REP-002 protocol verification failed: {exc}")
        return 2
    source_mode = " plus clean checkout" if args.lean_checkout else " from committed Git tree"
    print(
        f"Stage 5B Sol REP-002 protocol verified{source_mode}: "
        f"{protocol['id']} {protocol['version']} {protocol['status']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
