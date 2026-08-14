#!/usr/bin/env python3
"""Audit retained Phase 4 blind-annotation snapshots and run metadata."""

from __future__ import annotations

import hashlib
import json
import sys
from collections import Counter
from datetime import datetime
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PRIVATE = ROOT / "heldout" / "private"
ALLOWED_TOP_LEVEL = {"cases", "guidance", "schemas", "repo-context", "output"}
EXPECTED_COUNTS = {
    "cases": 48,
    "guidance": 3,
    "schemas": 2,
    "repo-context": 7,
    "output": 16,
}


def fail(message: str) -> None:
    raise RuntimeError(message)


def snapshot_digest(root: Path) -> str:
    records = []
    for path in sorted(candidate for candidate in root.rglob("*") if candidate.is_file()):
        records.append(
            f"{path.relative_to(root)}\t{hashlib.sha256(path.read_bytes()).hexdigest()}"
        )
    return hashlib.sha256(("\n".join(records) + "\n").encode()).hexdigest()


def main() -> int:
    try:
        snapshots = {
            "annotator_a": Path("/tmp/msb-phase4-annotator-a.BleVlf"),
            "annotator_b": Path("/tmp/msb-phase4-annotator-b.4NpO2v"),
        }
        digests = {}
        for alias, snapshot in snapshots.items():
            if not snapshot.is_dir():
                fail(f"retained isolation snapshot missing: {snapshot}")
            top_level = {path.name for path in snapshot.iterdir()}
            if top_level != ALLOWED_TOP_LEVEL:
                fail(f"unexpected snapshot categories for {alias}: {sorted(top_level)}")
            counts = {
                name: sum(path.is_file() for path in (snapshot / name).rglob("*"))
                for name in ALLOWED_TOP_LEVEL
            }
            if counts != EXPECTED_COUNTS:
                fail(f"snapshot inventory drift for {alias}: {counts}")
            record = json.loads(
                (PRIVATE / "annotation-runs" / f"{alias}.json").read_text(encoding="utf-8")
            )
            digest = snapshot_digest(snapshot)
            if digest != record["snapshot_inventory_sha256_auditor_contract"]:
                fail(f"snapshot hash drift for {alias}")
            annotations = [
                json.loads(path.read_text(encoding="utf-8"))
                for path in sorted((snapshot / "output").glob("*.json"))
            ]
            if len(annotations) != 16 or any(a["saw_other_annotation"] for a in annotations):
                fail(f"annotation independence field failed for {alias}")
            confidence = Counter(annotation["confidence"] for annotation in annotations)
            if dict(confidence) != {"HIGH": 14, "MEDIUM": 2}:
                fail(f"confidence inventory drift for {alias}: {dict(confidence)}")
            submitted = [datetime.fromisoformat(a["submitted_at"].replace("Z", "+00:00"))
                         for a in annotations]
            start = datetime.fromisoformat(record["earliest_start_proxy"].replace("Z", "+00:00"))
            finish = datetime.fromisoformat(record["latest_submitted_at"].replace("Z", "+00:00"))
            if min(submitted) < start or max(submitted) != finish:
                fail(f"annotation time chain failed for {alias}")
            digests[alias] = digest
        if digests["annotator_a"] == digests["annotator_b"]:
            fail("annotator snapshots are unexpectedly byte-identical")
        print(
            "annotation isolation passed: two distinct 76-file snapshots; "
            "16 outputs each; no cross-annotation visibility"
        )
        return 0
    except (OSError, ValueError, KeyError, RuntimeError) as exc:
        print(f"annotation isolation failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
