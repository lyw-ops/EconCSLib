#!/usr/bin/env python3
"""Run the R000 non-authoritative shadow adapter for one candidate."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


SCRIPT_ROOT = Path(__file__).resolve().parent
if str(SCRIPT_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPT_ROOT))

from rubric_common import R000_PATH, canonical_json_bytes, evaluate_shadow  # noqa: E402


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--route", choices=("direct", "transport"), required=True)
    parser.add_argument("--candidate-dir", type=Path, required=True)
    parser.add_argument("--candidate-id", required=True)
    parser.add_argument("--rubric", type=Path, default=R000_PATH)
    parser.add_argument("--output", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    result = evaluate_shadow(args.route, args.candidate_dir, args.candidate_id, args.rubric)
    encoded = canonical_json_bytes(result)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(encoded)
    sys.stdout.buffer.write(encoded)
    return 0 if result["hard_oracle"]["status"] != "error" else 2


if __name__ == "__main__":
    raise SystemExit(main())
