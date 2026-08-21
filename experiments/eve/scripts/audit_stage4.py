#!/usr/bin/env python3
"""Audit and independently re-evaluate the frozen Stage 4 run matrix."""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


SCRIPT_ROOT = Path(__file__).resolve().parent
SIDECAR_ROOT = SCRIPT_ROOT.parent
REPO_ROOT = SIDECAR_ROOT.parents[1]
PROTOCOL_PATH = SIDECAR_ROOT / "stage4_protocol.json"
PROTOCOL_ID = "EVE-STAGE4-LUNA-ENTRY-GAME-DEV-002"
STREAM_NAMES = ("solver_population", "optimizer_population", "worker_selection")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def derive_stream_seed(experiment_seed: int, stream_name: str) -> int:
    material = f"EconCSlib-EvE-Stage4-v1:{experiment_seed}:{stream_name}".encode()
    return int.from_bytes(hashlib.sha256(material).digest()[:8], "big")


def load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"expected JSON object: {path}")
    return payload


def fail_unless(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def load_evaluator():
    path = SCRIPT_ROOT / "evaluate_stage2_entry_game.py"
    spec = importlib.util.spec_from_file_location("stage4_entry_game_evaluator", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load Stage 2 evaluator")
    if str(SCRIPT_ROOT) not in sys.path:
        sys.path.insert(0, str(SCRIPT_ROOT))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def expected_matrix(protocol: dict[str, Any]) -> dict[tuple[str, str, int], int]:
    matrix: dict[tuple[str, str, int], int] = {}
    for item in protocol["run_matrix"]:
        key = (item["task"], item["condition"], int(item["seed"]))
        fail_unless(key not in matrix, f"duplicate protocol cell: {key}")
        matrix[key] = int(item["ordinal"])
    fail_unless(len(matrix) == 12, "protocol matrix is not 12 cells")
    return matrix


def score_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def audit_runs(runs_root: Path, *, recheck: bool) -> dict[str, Any]:
    protocol = load_json(PROTOCOL_PATH)
    fail_unless(protocol.get("id") == PROTOCOL_ID, "protocol identity mismatch")
    matrix = expected_matrix(protocol)
    current_protocol_hash = sha256(PROTOCOL_PATH)
    evaluator = load_evaluator() if recheck else None

    launches: dict[tuple[str, str, int], tuple[Path, dict[str, Any]]] = {}
    excluded_protocols: Counter[str] = Counter()
    for launch_path in sorted(runs_root.glob("*/stage4-launch.json")):
        launch = load_json(launch_path)
        launch_protocol = str(launch.get("protocol_id", "missing"))
        if launch_protocol != PROTOCOL_ID:
            excluded_protocols[launch_protocol] += 1
            continue
        key = (
            str(launch["experiment"]),
            str(launch["condition"]),
            int(launch["experiment_seed"]),
        )
        fail_unless(key not in launches, f"duplicate DEV-002 launch: {key}")
        launches[key] = (launch_path, launch)
    fail_unless(set(launches) == set(matrix), "executed matrix differs from protocol")

    cells: list[dict[str, Any]] = []
    failure_counts: Counter[str] = Counter()
    grouped: dict[tuple[str, str], list[bool]] = defaultdict(list)
    total_turns = 0
    total_wallclock = 0.0
    total_output_tokens = 0
    total_passed_candidates = 0
    total_optimizer_candidates = 0

    for key, ordinal in sorted(matrix.items(), key=lambda item: item[1]):
        task, condition, seed = key
        launch_path, launch = launches[key]
        run_root = launch_path.parent
        route = "direct" if task.endswith("direct") else "transport"

        fail_unless(launch.get("status") == "completed", f"cell {ordinal} not completed")
        fail_unless(launch.get("exit_code") == 0, f"cell {ordinal} nonzero exit")
        fail_unless(launch.get("attempt_limit") == 1, f"cell {ordinal} attempt drift")
        fail_unless(launch.get("resume") is False, f"cell {ordinal} used resume")
        fail_unless(launch.get("import") is False, f"cell {ordinal} used import")
        fail_unless(launch.get("iterations") == 2, f"cell {ordinal} iteration drift")
        fail_unless(launch.get("model") == "gpt-5.6-luna", f"cell {ordinal} model drift")
        fail_unless(launch.get("reasoning_effort") == "low", f"cell {ordinal} effort drift")
        fail_unless(
            launch.get("protocol_sha256") == current_protocol_hash,
            f"cell {ordinal} protocol hash drift",
        )
        command = launch.get("command")
        fail_unless(isinstance(command, list), f"cell {ordinal} command missing")
        command_text = [str(part) for part in command]
        for required in (
            "--offline",
            "--frozen",
            "--no-sync",
            f"condition={condition}",
            f"experiment_seed={seed}",
        ):
            fail_unless(required in command_text, f"cell {ordinal} command drift: {required}")
        fail_unless(
            not any(part.startswith("resume_from=") for part in command_text),
            f"cell {ordinal} command used resume",
        )
        fail_unless(
            not any(part.startswith("import_from=") for part in command_text),
            f"cell {ordinal} command used import",
        )

        seed_path = run_root / "eve-sampler-seed.json"
        seed_audit = load_json(seed_path)
        fail_unless(seed_audit.get("experiment_seed") == seed, f"cell {ordinal} seed mismatch")
        expected_seeds = {
            stream: derive_stream_seed(seed, stream) for stream in STREAM_NAMES
        }
        fail_unless(
            seed_audit.get("derived_stream_seeds") == expected_seeds,
            f"cell {ordinal} derived seed mismatch",
        )
        fail_unless(
            seed_audit.get("seeded_before_initial_guidance_and_loop") is True,
            f"cell {ordinal} seed timing mismatch",
        )

        rows = score_rows(run_root / "telemetry" / "phase2_solvers.csv")
        fail_unless(len(rows) == 2, f"cell {ordinal} does not have two solver rows")
        fail_unless(
            [int(row["iteration"]) for row in rows] == [1, 2],
            f"cell {ordinal} iteration sequence mismatch",
        )
        optimizer_rows = score_rows(run_root / "telemetry" / "phase2_optimizers.csv")
        total_optimizer_candidates += len(optimizer_rows)

        candidate_records: list[dict[str, Any]] = []
        for row in rows:
            iteration = int(row["iteration"])
            workspace_id = row["workspace_id"]
            archived_path = (
                run_root
                / "evaluation_workspaces"
                / workspace_id
                / "logs"
                / "evaluate"
                / "evaluation.json"
            )
            candidate_dir = (
                run_root / "evaluation_workspaces" / workspace_id / "solver"
            )
            candidate_path = candidate_dir / "Candidate.lean"
            token_path = (
                run_root
                / "solver_workspaces"
                / workspace_id
                / "logs"
                / "optimize"
                / "token_usage.json"
            )
            archived = load_json(archived_path)
            score = json.loads(row["score_json"])
            fail_unless(archived.get("route") == route, f"cell {ordinal} route mismatch")
            fail_unless(
                float(archived.get("score", -1)) == float(score["score"]),
                f"cell {ordinal} score mismatch at iteration {iteration}",
            )
            passed = archived.get("status") == "passed"
            fail_unless(
                passed == (float(score["score"]) == 1.0),
                f"cell {ordinal} status mismatch at iteration {iteration}",
            )
            if passed:
                fail_unless(
                    all(archived["gates"].values()),
                    f"cell {ordinal} false accept at iteration {iteration}",
                )
                fail_unless(
                    archived.get("failure_codes") == [],
                    f"cell {ordinal} passed with failure codes",
                )
                total_passed_candidates += 1
            else:
                fail_unless(
                    bool(archived.get("failure_codes")),
                    f"cell {ordinal} failed without failure code",
                )
                failure_counts.update(archived["failure_codes"])

            if evaluator is not None:
                fresh = evaluator.evaluate_candidate(route, candidate_dir)
                for field in ("status", "score", "failure_codes", "gates", "axioms"):
                    fail_unless(
                        fresh.get(field) == archived.get(field),
                        f"cell {ordinal} recheck mismatch ({field}) at iteration {iteration}",
                    )

            token_usage = load_json(token_path)
            attempts = token_usage.get("attempts")
            fail_unless(
                isinstance(attempts, list) and len(attempts) == 1,
                f"cell {ordinal} token attempt mismatch at iteration {iteration}",
            )
            turns = int(float(row["agent_turns"]))
            fail_unless(turns <= 6, f"cell {ordinal} exceeded turn limit")
            wallclock = float(row["wallclock_seconds"])
            output_tokens = int(float(row["output_tokens"]))
            total_turns += turns
            total_wallclock += wallclock
            total_output_tokens += output_tokens
            candidate_records.append(
                {
                    "iteration": iteration,
                    "solver_id": row["solver_id"],
                    "workspace_id": workspace_id,
                    "status": archived["status"],
                    "score": archived["score"],
                    "failure_codes": archived["failure_codes"],
                    "agent_turns": turns,
                    "wallclock_seconds": wallclock,
                    "output_tokens": output_tokens,
                    "candidate_sha256": sha256(candidate_path),
                    "evaluation_sha256": sha256(archived_path),
                    "candidate_path": candidate_path.relative_to(REPO_ROOT).as_posix(),
                }
            )

        primary_success = any(item["status"] == "passed" for item in candidate_records)
        first_success = next(
            (item["iteration"] for item in candidate_records if item["status"] == "passed"),
            None,
        )
        grouped[(task, condition)].append(primary_success)
        cells.append(
            {
                "ordinal": ordinal,
                "task": task,
                "condition": condition,
                "seed": seed,
                "run_root": run_root.relative_to(REPO_ROOT).as_posix(),
                "launch_sha256": sha256(launch_path),
                "seed_audit_sha256": sha256(seed_path),
                "primary_success": primary_success,
                "first_success_iteration": first_success,
                "optimizer_candidates_produced": len(optimizer_rows),
                "candidates": candidate_records,
            }
        )

    grouped_summary = []
    for (task, condition), outcomes in sorted(grouped.items()):
        fail_unless(len(outcomes) == 2, f"group {(task, condition)} is not n=2")
        grouped_summary.append(
            {
                "task": task,
                "condition": condition,
                "successes": sum(outcomes),
                "runs": len(outcomes),
                "descriptive_rate": sum(outcomes) / len(outcomes),
            }
        )

    return {
        "schema_version": "1.0.0",
        "audit_status": "passed",
        "protocol_id": PROTOCOL_ID,
        "protocol_sha256": current_protocol_hash,
        "review_kind": "deterministic-machine-audit-plus-codex-ai-source-review-pending",
        "independent_human_review": False,
        "rechecked_all_candidates": recheck,
        "matrix": {
            "expected_cells": 12,
            "completed_unique_cells": len(cells),
            "solver_candidates": sum(len(cell["candidates"]) for cell in cells),
            "maximum_model_sessions": protocol["maximum_model_sessions"],
            "resume_or_import_used": False,
            "duplicate_dev002_cells": 0,
            "excluded_launches_by_protocol": dict(sorted(excluded_protocols.items())),
        },
        "totals": {
            "successful_runs": sum(cell["primary_success"] for cell in cells),
            "failed_runs": sum(not cell["primary_success"] for cell in cells),
            "passed_candidates": total_passed_candidates,
            "failed_candidates": 24 - total_passed_candidates,
            "agent_turns": total_turns,
            "solver_wallclock_seconds": round(total_wallclock, 6),
            "output_tokens": total_output_tokens,
            "optimizer_candidates_produced": total_optimizer_candidates,
        },
        "failure_code_counts": dict(sorted(failure_counts.items())),
        "grouped_outcomes": grouped_summary,
        "cells": cells,
        "claim_boundary": protocol["claim_boundary"],
    }


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument(
        "--runs-root",
        type=Path,
        default=SIDECAR_ROOT / ".runtime" / "runs",
    )
    result.add_argument("--output", type=Path)
    result.add_argument("--no-recheck", action="store_true")
    return result


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        report = audit_runs(args.runs_root.resolve(), recheck=not args.no_recheck)
    except (OSError, ValueError, RuntimeError, json.JSONDecodeError) as exc:
        print(f"Stage 4 audit failed: {exc}", file=sys.stderr)
        return 1
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
