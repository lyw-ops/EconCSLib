#!/usr/bin/env python3
"""Run pinned EvE with DEV-003 fail-closed liveness telemetry."""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import re
import threading
from pathlib import Path
from typing import Any

import hydra
from omegaconf import OmegaConf

from scaling_evolve.algorithms.eve import runner
from scaling_evolve.algorithms.eve.factory import EveFactory
from scaling_evolve.algorithms.eve.workflow.phase2 import Phase2BatchRunner, Phase2Runner


STREAM_NAMES = ("solver_population", "optimizer_population", "worker_selection")
EXPECTED_PYTHON_VERSION = "3.9.6"
EXPECTED_PYTHON_INVOCATION = "/usr/bin/python3"
EXPECTED_PYTHON_EXECUTABLE = "/Library/Developer/CommandLineTools/usr/bin/python3"
EXPECTED_CHECK_COMMAND = ["lake", "env", "lean", "solver/Candidate.lean"]
_HEX64 = re.compile(r"[0-9a-f]{64}")
_ORIGINAL_FROM_CONFIG = EveFactory.from_config.__func__
_ORIGINAL_SAMPLE_OPTIMIZERS = Phase2BatchRunner._sample_optimizers
_ORIGINAL_ADD_OPTIMIZERS = Phase2BatchRunner._add_selected_phase2_optimizers
_ORIGINAL_BUILD_WORKSPACE = Phase2Runner._build_workspace
_ORIGINAL_RUN_SINGLE = Phase2Runner.run_single
_EVENT_LOCK = threading.Lock()


def tree_sha256(files: dict[str, str]) -> str:
    """Hash an in-memory guidance tree with stable path and length framing."""
    digest = hashlib.sha256()
    for relative, content in sorted(files.items()):
        relative_bytes = relative.encode("utf-8")
        content_bytes = content.encode("utf-8")
        digest.update(len(relative_bytes).to_bytes(8, "big"))
        digest.update(relative_bytes)
        digest.update(len(content_bytes).to_bytes(8, "big"))
        digest.update(content_bytes)
    return digest.hexdigest()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def local_event_sha256(event: dict[str, object]) -> str:
    payload = {key: value for key, value in event.items() if key != "event_sha256"}
    encoded = json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def derive_stream_seed(experiment_seed: int, stream_name: str) -> int:
    if stream_name not in STREAM_NAMES:
        raise ValueError("unknown EvE RNG stream")
    material = (
        f"EconCSlib-EvE-Stage5A-DEV003-v1:{experiment_seed}:{stream_name}"
    ).encode()
    return int.from_bytes(hashlib.sha256(material).digest()[:8], "big")


def seed_factory(factory: Any, experiment_seed: int) -> dict[str, int]:
    if isinstance(experiment_seed, bool) or not 0 <= experiment_seed < 2**63:
        raise ValueError("experiment_seed must be an integer in [0, 2^63)")
    seeds = {
        name: derive_stream_seed(experiment_seed, name) for name in STREAM_NAMES
    }
    factory.loop.solver_pop._rng.seed(seeds["solver_population"])
    factory.loop.optimizer_pop._rng.seed(seeds["optimizer_population"])
    factory.loop.solver_workspace_builder._rng.seed(seeds["worker_selection"])
    return seeds


def _event_path() -> Path:
    value = __import__("os").environ.get("EVE_STAGE5A_OBSERVATION_PATH")
    if not value:
        raise RuntimeError("EVE_STAGE5A_OBSERVATION_PATH is required")
    return Path(value).resolve()


def _record(event: dict[str, object]) -> None:
    payload = {"schema_version": "2.0.0", **event}
    path = _event_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    with _EVENT_LOCK, path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, sort_keys=True) + "\n")


def _entry_record(entry: object) -> dict[str, object]:
    files = dict(getattr(entry, "files"))
    return {
        "optimizer_id": str(getattr(entry, "id")),
        "guidance_sha256": tree_sha256(files),
    }


def _observed_sample_optimizers(self):
    population_before = [_entry_record(entry) for entry in self.optimizer_pop.entries()]
    sampled = _ORIGINAL_SAMPLE_OPTIMIZERS(self)
    _record(
        {
            "event": "working_optimizer_sampled",
            "iteration": self.iteration,
            "population_before": population_before,
            "sampled": [_entry_record(entry) for entry in sampled],
        }
    )
    return sampled


def _observed_build_workspace(self) -> None:
    _ORIGINAL_BUILD_WORKSPACE(self)
    if self.workspace is None or self.optimizer is None:
        raise RuntimeError("DEV-003 workspace observation requires a built workspace")
    loaded_files = self.solver_workspace_builder.extract_optimizer(
        self.workspace, worker_config=self.worker_config
    )
    checker = self.workspace / "STAGE5A_LEAN_CHECK.py"
    if not checker.is_file():
        raise RuntimeError("DEV-003 immutable Lean checker is missing")
    checker_hash = file_sha256(checker)
    self._stage5a_checker_sha256 = checker_hash
    _record(
        {
            "event": "solver_guidance_loaded",
            "iteration": self.iteration,
            "workspace_id": self.workspace.name,
            **_entry_record(self.optimizer),
            "workspace_guidance_sha256": tree_sha256(loaded_files),
            "matches_sampled_optimizer": loaded_files == self.optimizer.files,
            "lean_checker_sha256": checker_hash,
        }
    )


def _load_lean_check_events(workspace: Path) -> list[dict[str, object]]:
    path = workspace / ".scaling_evolve" / "stage5a-lean-checks.jsonl"
    if not path.is_file():
        raise RuntimeError("required DEV-003 Lean-check evidence is missing")
    lines = [line for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
    if not lines:
        raise RuntimeError("required DEV-003 Lean-check evidence is empty")
    events: list[dict[str, object]] = []
    for line in lines:
        try:
            value = json.loads(line)
        except json.JSONDecodeError as exc:
            raise RuntimeError("DEV-003 Lean-check evidence is malformed") from exc
        if not isinstance(value, dict):
            raise RuntimeError("DEV-003 Lean-check event is not an object")
        events.append(value)
    return events


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and _HEX64.fullmatch(value) is not None


def _validate_lean_check_events(
    events: list[dict[str, object]],
    *,
    checker_sha256: str,
    final_candidate_sha256: str,
) -> None:
    if not events:
        raise RuntimeError("required DEV-003 Lean-check evidence is empty")
    previous: str | None = None
    for sequence, event in enumerate(events, start=1):
        if event.get("schema_version") != "2.0.0":
            raise RuntimeError("DEV-003 Lean-check schema is invalid")
        if event.get("sequence") != sequence:
            raise RuntimeError("DEV-003 Lean-check sequence is not contiguous")
        if event.get("previous_event_sha256") != previous:
            raise RuntimeError("DEV-003 Lean-check hash chain is invalid")
        if event.get("checker_sha256") != checker_sha256:
            raise RuntimeError("DEV-003 Lean check used a different checker")
        if event.get("event_sha256") != local_event_sha256(event):
            raise RuntimeError("DEV-003 Lean-check event hash is invalid")
        for key in (
            "candidate_sha256",
            "guidance_sha256",
            "stdout_sha256",
            "stderr_sha256",
            "event_sha256",
        ):
            if not _is_hash(event.get(key)):
                raise RuntimeError(f"DEV-003 Lean-check {key} is invalid")
        if event.get("python_invocation") != EXPECTED_PYTHON_INVOCATION:
            raise RuntimeError("DEV-003 checker invocation drifted")
        if event.get("python_executable") != EXPECTED_PYTHON_EXECUTABLE:
            raise RuntimeError("DEV-003 checker executable drifted")
        if event.get("python_version") != EXPECTED_PYTHON_VERSION:
            raise RuntimeError("DEV-003 checker Python version drifted")
        if event.get("command") != EXPECTED_CHECK_COMMAND:
            raise RuntimeError("DEV-003 Lean command drifted")
        exit_code = event.get("exit_code")
        failed = event.get("failed")
        if isinstance(exit_code, bool) or not isinstance(exit_code, int):
            raise RuntimeError("DEV-003 Lean-check exit status is invalid")
        if not isinstance(failed, bool) or failed != (exit_code != 0):
            raise RuntimeError("DEV-003 Lean-check failure flag is inconsistent")
        for key in ("stdout_bytes", "stderr_bytes"):
            value = event.get(key)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise RuntimeError(f"DEV-003 Lean-check {key} is invalid")
        observed = event.get("observed_at")
        try:
            instant = dt.datetime.fromisoformat(str(observed))
        except ValueError as exc:
            raise RuntimeError("DEV-003 Lean-check timestamp is malformed") from exc
        if instant.utcoffset() != dt.timedelta(0):
            raise RuntimeError("DEV-003 Lean-check timestamp is not UTC")
        previous = str(event["event_sha256"])
    if events[-1].get("candidate_sha256") != final_candidate_sha256:
        raise RuntimeError("DEV-003 final checker event does not match final candidate")


def _observed_run_single(self, **kwargs):
    result = _ORIGINAL_RUN_SINGLE(self, **kwargs)
    if self.workspace is None or self.optimizer is None:
        raise RuntimeError("DEV-003 rollout observation requires a workspace")
    candidate_path = self.workspace / "solver" / "Candidate.lean"
    if not candidate_path.is_file():
        raise RuntimeError("DEV-003 final candidate is missing")
    final_candidate_hash = file_sha256(candidate_path)
    final_files = self.solver_workspace_builder.extract_optimizer(
        self.workspace, worker_config=self.worker_config
    )
    lean_checks = _load_lean_check_events(self.workspace)
    checker = self.workspace / "STAGE5A_LEAN_CHECK.py"
    final_checker_hash = file_sha256(checker) if checker.is_file() else None
    initial_checker_hash = getattr(self, "_stage5a_checker_sha256", None)
    if final_checker_hash is None or final_checker_hash != initial_checker_hash:
        raise RuntimeError("DEV-003 immutable Lean checker changed during rollout")
    _validate_lean_check_events(
        lean_checks,
        checker_sha256=final_checker_hash,
        final_candidate_sha256=final_candidate_hash,
    )
    failures = [event for event in lean_checks if event.get("failed") is True]
    final_guidance_hash = tree_sha256(final_files)
    failure_before_change = [
        event
        for event in failures
        if event.get("guidance_sha256") != final_guidance_hash
    ]
    failure_hashes = [str(event["event_sha256"]) for event in failure_before_change]
    _record(
        {
            "event": "solver_rollout_completed",
            "iteration": self.iteration,
            "workspace_id": self.workspace.name,
            "working_optimizer_id": self.optimizer.id,
            "initial_guidance_sha256": tree_sha256(self.optimizer.files),
            "final_guidance_sha256": final_guidance_hash,
            "final_candidate_sha256": final_candidate_hash,
            "guidance_tree_changed": final_files != self.optimizer.files,
            "check_evidence_required": True,
            "check_evidence_validated": True,
            "local_lean_checks": lean_checks,
            "recorded_local_lean_failures": len(failures),
            "failure_before_guidance_change": bool(failure_before_change),
            "failure_before_guidance_change_sequences": [
                event["sequence"] for event in failure_before_change
            ],
            "failure_event_hashes": failure_hashes,
            "lean_checker_sha256": final_checker_hash,
            "lean_checker_unchanged": True,
            "produced_solver_id": (
                result.produced_solver.id if result.produced_solver is not None else None
            ),
        }
    )
    if result.produced_optimizer is not None:
        candidate = result.produced_optimizer
        _record(
            {
                "event": "optimizer_candidate_produced",
                "source_iteration": self.iteration,
                "workspace_id": self.workspace.name,
                "parent_optimizer_id": self.optimizer.id,
                "parent_guidance_sha256": tree_sha256(self.optimizer.files),
                "candidate_id": candidate.id,
                "candidate_guidance_sha256": tree_sha256(candidate.files),
                "produced_solver_id": (
                    result.produced_solver.id
                    if result.produced_solver is not None
                    else None
                ),
                "check_evidence_validated": True,
                "recorded_local_lean_failures": len(failures),
                "failure_before_guidance_change": bool(failure_before_change),
                "failure_before_guidance_change_sequences": [
                    event["sequence"] for event in failure_before_change
                ],
                "failure_event_hashes": failure_hashes,
            }
        )
    return result


def _observed_add_optimizers(self, results) -> None:
    produced = []
    for result in results:
        candidate = result.produced_optimizer
        if candidate is not None:
            produced.append(
                {
                    "candidate_id": candidate.id,
                    "candidate_guidance_sha256": tree_sha256(candidate.files),
                }
            )
    _ORIGINAL_ADD_OPTIMIZERS(self, results)
    population = {entry.id: entry for entry in self.optimizer_pop.entries()}
    for candidate in produced:
        entry = population.get(str(candidate["candidate_id"]))
        admitted = entry is not None
        _record(
            {
                "event": "optimizer_population_admission",
                "source_iteration": self.iteration,
                **candidate,
                "admitted": admitted,
                "population_guidance_sha256": (
                    tree_sha256(entry.files) if entry is not None else None
                ),
            }
        )


def _seeded_from_config(cls, config, solver_evaluator, **kwargs):
    factory = _ORIGINAL_FROM_CONFIG(cls, config, solver_evaluator, **kwargs)
    raw_seed = OmegaConf.select(config, "experiment_seed")
    if isinstance(raw_seed, bool) or not isinstance(raw_seed, int):
        factory.close()
        raise SystemExit("DEV-003 requires an integer experiment_seed")
    condition = OmegaConf.to_container(
        OmegaConf.select(config, "stage5a_condition"), resolve=True
    )
    if not isinstance(condition, dict):
        factory.close()
        raise SystemExit("DEV-003 requires stage5a_condition metadata")
    try:
        derived = seed_factory(factory, raw_seed)
    except ValueError as exc:
        factory.close()
        raise SystemExit(str(exc)) from exc
    run_root = Path(str(config.run_root)).resolve()
    audit = {
        "schema_version": "2.0.0",
        "protocol_generation": "DEV-003",
        "experiment_seed": raw_seed,
        "derived_stream_seeds": derived,
        "seeded_before_initial_guidance_and_loop": True,
        "controlled_scope": "EvE sampler and worker-selection random.Random streams",
        "provider_model_seed_controlled": False,
        "uncontrolled_scope": "Codex/provider model sampling; pinned adapter exposes no model seed",
        "condition": condition,
    }
    audit_path = run_root / "eve-stage5a-sampler-seed.json"
    audit_path.parent.mkdir(parents=True, exist_ok=True)
    audit_path.write_text(
        json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    _record(
        {
            "event": "factory_seeded",
            "experiment_seed": raw_seed,
            "condition": condition,
            "derived_stream_seeds": derived,
            "provider_model_seed_controlled": False,
        }
    )
    return factory


EveFactory.from_config = classmethod(_seeded_from_config)
runner.EveFactory = EveFactory
Phase2BatchRunner._sample_optimizers = _observed_sample_optimizers
Phase2BatchRunner._add_selected_phase2_optimizers = _observed_add_optimizers
Phase2Runner._build_workspace = _observed_build_workspace
Phase2Runner.run_single = _observed_run_single


@hydra.main(version_base="1.3", config_path=None)
def main(config) -> None:
    runner.run(config)


if __name__ == "__main__":
    main()
