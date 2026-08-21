#!/usr/bin/env python3
"""Fail-closed consistency check for the Stage 3 Codex review record."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


SIDECAR_ROOT = Path(__file__).resolve().parent.parent
REVIEW_ROOT = SIDECAR_ROOT / "stage3_review"
TASK_ROOT = SIDECAR_ROOT / "stage2_entry_game"


def _load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("JSON root must be an object")
    return value


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify() -> dict[str, Any]:
    failures: list[str] = []
    rubric = _load(REVIEW_ROOT / "rubric.json")
    record = _load(REVIEW_ROOT / "review-record.json")
    corpus_path = TASK_ROOT / "mutations.json"
    corpus = _load(corpus_path)
    protected = record.get("protected_inputs", {})

    expected_hashes = {
        "source_lock_sha256": _sha(TASK_ROOT / "source-lock.json"),
        "mutations_sha256": _sha(corpus_path),
        "direct_accepted_sha256": _sha(
            TASK_ROOT / "direct" / "expected" / "Accepted.lean"
        ),
        "transport_accepted_sha256": _sha(
            TASK_ROOT / "transport" / "expected" / "Accepted.lean"
        ),
    }
    if protected != expected_hashes:
        failures.append("protected-review-input-hash-mismatch")
    if rubric.get("reviewer_kind") != "codex-ai-review":
        failures.append("reviewer-kind-invalid")
    if record.get("reviewer", {}).get("independent_human_review") is not False:
        failures.append("human-review-claim-invalid")

    expected_mutations = {item["id"] for item in corpus.get("mutations", [])}
    reviewed_mutations = {
        item.get("id")
        for item in record.get("mutation_reviews", [])
        if item.get("decision") == "reject" and item.get("severity") in {"P1", "P2"}
    }
    if reviewed_mutations != expected_mutations:
        failures.append("mutation-review-coverage-incomplete")

    accepted = record.get("accepted_candidates", [])
    if {item.get("id") for item in accepted} != {
        "DIRECT-ACCEPTED", "TRANSPORT-ACCEPTED"
    }:
        failures.append("accepted-review-coverage-incomplete")
    if any(
        item.get("decision") != "accept" or item.get("blocking_findings") != []
        for item in accepted
    ):
        failures.append("accepted-review-decision-invalid")

    passed = not failures
    return {
        "schema_version": "1.0.0",
        "review_id": record.get("id"),
        "status": "passed" if passed else "failed",
        "score": 1.0 if passed else 0.0,
        "failure_codes": failures,
        "metrics": {
            "accepted_review_recall": len(accepted) / 2,
            "mutation_rejection_recall": (
                len(reviewed_mutations) / len(expected_mutations)
                if expected_mutations else 0.0
            ),
            "blocking_false_accepts": record.get("metrics", {}).get(
                "blocking_false_accepts"
            ),
        },
        "reviewer": record.get("reviewer"),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        report = verify()
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        report = {
            "schema_version": "1.0.0",
            "status": "failed",
            "score": 0.0,
            "failure_codes": [f"review-input-error:{type(exc).__name__}"],
        }
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    print(f"Stage 3 review verification: {report['status']} (score={report['score']:.1f})")
    if report["failure_codes"]:
        print("Failure codes: " + ", ".join(report["failure_codes"]))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
