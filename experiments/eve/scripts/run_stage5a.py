#!/usr/bin/env python3
"""Independent safe entrypoint for the frozen, not-yet-executed Stage 5A protocol."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = SIDECAR_ROOT.parents[1]
CONFIG_ROOT = SIDECAR_ROOT / "configs" / "eve"
OVERLAY_ROOT = SIDECAR_ROOT / "overlay"
RUNS_ROOT = SIDECAR_ROOT / ".runtime" / "stage5a-runs"
PROTOCOL_PATH = SIDECAR_ROOT / "stage5a_protocol.json"
PROTOCOL_HASH_PATH = SIDECAR_ROOT / "stage5a_protocol.sha256"
SEMANTICS_PATH = SIDECAR_ROOT / "stage5a_upstream_semantics.json"
PROTOCOL_ID = "EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-001"
PROTOCOL_VERSION = "1.0.0"
CONDITIONS = ("static", "fixed", "evolved")
SEEDS = (1729, 2718)
ITERATIONS = 3


def _load_stage4_runner():
    path = SIDECAR_ROOT / "scripts" / "run.py"
    spec = importlib.util.spec_from_file_location("eve_stage4_frozen_runner", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load frozen helper runner {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules["eve_stage4_frozen_runner"] = module
    spec.loader.exec_module(module)
    return module


BASE = _load_stage4_runner()
CheckError = BASE.CheckError


@dataclass(frozen=True)
class Stage5ASpec:
    cli_name: str
    route: str
    config_name: str
    overlay_key: str
    seed_root: Path
    accepted_fixture: Path
    evaluator: Path
    evaluation_step: Path


TASK_ROOT = SIDECAR_ROOT / "stage2_entry_game"
SPECS = {
    "entry-game-direct": Stage5ASpec(
        cli_name="entry-game-direct",
        route="direct",
        config_name="entry_game_direct_stage5a",
        overlay_key="stage5a_entry_game_direct",
        seed_root=TASK_ROOT / "direct" / "seed",
        accepted_fixture=TASK_ROOT / "direct" / "expected" / "Accepted.lean",
        evaluator=SIDECAR_ROOT / "scripts" / "evaluate_stage2_entry_game.py",
        evaluation_step=SIDECAR_ROOT / "scripts" / "evaluation_stage2_entry_direct.sh",
    ),
    "entry-game-transport": Stage5ASpec(
        cli_name="entry-game-transport",
        route="transport",
        config_name="entry_game_transport_stage5a",
        overlay_key="stage5a_entry_game_transport",
        seed_root=TASK_ROOT / "transport" / "seed",
        accepted_fixture=TASK_ROOT / "transport" / "expected" / "Accepted.lean",
        evaluator=SIDECAR_ROOT / "scripts" / "evaluate_stage2_entry_game.py",
        evaluation_step=SIDECAR_ROOT / "scripts" / "evaluation_stage2_entry_transport.sh",
    ),
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(65536):
            digest.update(chunk)
    return digest.hexdigest()


def tree_sha256(root: Path) -> str:
    digest = hashlib.sha256()
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        relative = path.relative_to(root).as_posix().encode("utf-8")
        content = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return digest.hexdigest()


def prompt_bundle_sha256(spec: Stage5ASpec) -> str:
    route_root = OVERLAY_ROOT / spec.overlay_key
    paths = [
        route_root / "immutable" / "AGENTS.md",
        route_root / "immutable" / "README.md",
        route_root / "immutable" / "STAGE5A_LEAN_CHECK.py",
        route_root / "prompt" / "ENTRYPOINT.md",
        route_root / "prompt" / "BOUNDARY_REPAIR.md",
        route_root / "prompt" / "budget" / "USER.md",
        route_root / "prompt" / "budget" / "TURN.md",
    ]
    checkpoint = route_root / "immutable" / "TRANSPORT_CHECKPOINTS.md"
    if checkpoint.is_file():
        paths.append(checkpoint)
    digest = hashlib.sha256()
    for path in sorted(paths):
        relative = path.relative_to(route_root).as_posix().encode("utf-8")
        content = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return digest.hexdigest()


def _is_relative_to(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def _protocol_hash() -> str:
    record = PROTOCOL_HASH_PATH.read_text(encoding="utf-8").split()
    if len(record) != 2 or record[1] != "experiments/eve/stage5a_protocol.json":
        raise CheckError("Stage 5A detached protocol hash record is invalid")
    actual = sha256(PROTOCOL_PATH)
    if record[0] != actual:
        raise CheckError("Stage 5A protocol hash mismatch")
    return actual


def verify_protocol_assets() -> dict[str, Any]:
    try:
        protocol = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CheckError("Stage 5A protocol is missing or invalid") from exc
    _protocol_hash()
    if protocol.get("id") != PROTOCOL_ID or protocol.get("version") != PROTOCOL_VERSION:
        raise CheckError("Stage 5A protocol identity or version mismatch")
    if protocol.get("status") != "FROZEN_NOT_YET_EXECUTED":
        raise CheckError("Stage 5A protocol is not frozen and unexecuted")
    frozen = protocol.get("frozen_artifacts")
    if not isinstance(frozen, dict) or not frozen:
        raise CheckError("Stage 5A protocol has no frozen artifacts")
    for relative, expected in frozen.items():
        if not isinstance(relative, str) or not isinstance(expected, str):
            raise CheckError("Stage 5A frozen artifact record is invalid")
        artifact = (REPO_ROOT / relative).resolve()
        if not _is_relative_to(artifact, REPO_ROOT.resolve()):
            raise CheckError("Stage 5A frozen artifact escaped EconCSLib")
        if not artifact.is_file() or sha256(artifact) != expected:
            raise CheckError(f"Stage 5A frozen artifact hash mismatch: {relative}")
    protected = protocol.get("protected_stage4_history")
    if not isinstance(protected, dict) or not protected:
        raise CheckError("Stage 5A protocol does not protect Stage 4 history")
    for relative, expected in protected.items():
        artifact = (REPO_ROOT / str(relative)).resolve()
        if not artifact.is_file() or sha256(artifact) != expected:
            raise CheckError(f"Stage 4 historical evidence changed: {relative}")
    prompt_hashes = protocol.get("solver_prompt_bundle_hashes")
    expected_prompt_hashes = {
        spec.route: prompt_bundle_sha256(spec) for spec in SPECS.values()
    }
    if prompt_hashes != expected_prompt_hashes:
        raise CheckError("Stage 5A solver prompt bundle hash mismatch")
    return protocol


def verify_upstream_semantics(identity) -> None:
    try:
        evidence = json.loads(SEMANTICS_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CheckError("Stage 5A upstream semantics evidence is invalid") from exc
    if evidence.get("upstream", {}).get("commit") != identity.commit:
        raise CheckError("Stage 5A semantics targets a different EvE commit")
    sources = evidence.get("source_evidence")
    if not isinstance(sources, list) or not sources:
        raise CheckError("Stage 5A semantics has no source evidence")
    for record in sources:
        if not isinstance(record, dict):
            raise CheckError("Stage 5A source evidence record is invalid")
        relative = record.get("path")
        expected = record.get("sha256")
        if not isinstance(relative, str) or not isinstance(expected, str):
            raise CheckError("Stage 5A source evidence record is incomplete")
        path = (identity.root / relative).resolve()
        if not _is_relative_to(path, identity.root.resolve()):
            raise CheckError("Stage 5A upstream source path escaped checkout")
        if not path.is_file() or sha256(path) != expected:
            raise CheckError(f"Stage 5A upstream source hash mismatch: {relative}")


def _required_paths(spec: Stage5ASpec) -> tuple[Path, ...]:
    route_root = OVERLAY_ROOT / spec.overlay_key
    paths = (
        CONFIG_ROOT / "runtime" / "sidecar.yaml",
        CONFIG_ROOT / "loop" / "stage5a.yaml",
        CONFIG_ROOT / "driver" / "codex_luna_stage5a.yaml",
        CONFIG_ROOT / "logger" / "local.yaml",
        CONFIG_ROOT / f"{spec.config_name}.yaml",
        CONFIG_ROOT / "application" / f"entry_game_{spec.route}.yaml",
        CONFIG_ROOT / "evaluation" / f"entry_game_{spec.route}.yaml",
        CONFIG_ROOT / "optimizer" / f"entry_game_{spec.route}_stage5a.yaml",
        *(CONFIG_ROOT / "stage5a_condition" / f"{name}.yaml" for name in CONDITIONS),
        route_root / "immutable" / "AGENTS.md",
        route_root / "immutable" / "README.md",
        route_root / "immutable" / "STAGE5A_LEAN_CHECK.py",
        route_root / "prompt" / "ENTRYPOINT.md",
        route_root / "prompt" / "BOUNDARY_REPAIR.md",
        route_root / "prompt" / "budget" / "USER.md",
        route_root / "prompt" / "budget" / "TURN.md",
        route_root / "initial_guidance" / "docs" / f"{spec.route}.md",
        spec.seed_root / "Candidate.lean",
        spec.seed_root / "README.md",
        spec.seed_root.parent / "case.json",
        spec.accepted_fixture,
        spec.evaluator,
        spec.evaluation_step,
        SIDECAR_ROOT / "scripts" / "run_stage5a_eve.py",
        SIDECAR_ROOT / "scripts" / "audit_stage5a.py",
        PROTOCOL_PATH,
        PROTOCOL_HASH_PATH,
        SEMANTICS_PATH,
    )
    if spec.route == "transport":
        return paths + (route_root / "immutable" / "TRANSPORT_CHECKPOINTS.md",)
    return paths


def verify_sidecar_assets(spec: Stage5ASpec) -> None:
    missing = [
        path.relative_to(REPO_ROOT).as_posix()
        for path in _required_paths(spec)
        if not path.is_file()
    ]
    if missing:
        raise CheckError("Missing Stage 5A assets: " + ", ".join(missing))
    case = json.loads((spec.seed_root.parent / "case.json").read_text(encoding="utf-8"))
    if case.get("editable_files") != ["Candidate.lean"] or case.get("editable_folders") != []:
        raise CheckError("Stage 5A solver boundary is not exactly Candidate.lean")


def validate_selection(
    *, protocol_id: str, condition: str, experiment_seed: int
) -> None:
    if protocol_id != PROTOCOL_ID:
        raise CheckError("Stage 5A protocol id mismatch")
    if condition not in CONDITIONS:
        raise CheckError("Stage 5A condition is not frozen")
    if experiment_seed not in SEEDS:
        raise CheckError("Stage 5A experiment seed is not frozen")


def _guidance_source(spec: Stage5ASpec, condition: str) -> Path:
    if condition == "static":
        return Path(tempfile.gettempdir()) / "stage5a-check-empty-guidance"
    return OVERLAY_ROOT / spec.overlay_key / "initial_guidance"


def _dependency_probe(identity, spec: Stage5ASpec, condition: str, seed: int) -> bool:
    uv = shutil.which("uv")
    if uv is None or not (identity.root / ".venv" / "bin" / "python").is_file():
        return False
    with tempfile.TemporaryDirectory(prefix="econcslib-stage5a-probe-") as raw_temp:
        temp_root = Path(raw_temp)
        guidance = (
            temp_root / "empty-guidance"
            if condition == "static"
            else OVERLAY_ROOT / spec.overlay_key / "initial_guidance"
        )
        guidance.mkdir(parents=True, exist_ok=True)
        env = {
            **os.environ,
            "EVE_ECONCSLIB_ROOT": str(REPO_ROOT),
            "EVE_RUNTIME_OVERLAY_ROOT": str(OVERLAY_ROOT),
            "EVE_SIDECAR_RUN_ROOT": str(temp_root / "run"),
            "EVE_STAGE5A_GUIDANCE_ROOT": str(guidance),
            "EVE_STAGE5A_OBSERVATION_PATH": str(temp_root / "events.jsonl"),
            "PYTHONPATH": str(identity.root / "src"),
        }
        script = f"""
import importlib.util
import random
from pathlib import Path
from types import SimpleNamespace
from hydra import compose, initialize_config_dir
from hydra.utils import instantiate
from scaling_evolve.algorithms.eve.factory import _load_solver_worker_configs
from scaling_evolve.algorithms.eve.workflow.evaluation import build_evaluation_plan

with initialize_config_dir(version_base='1.3', config_dir={str(CONFIG_ROOT)!r}):
    config = compose(
        config_name={spec.config_name!r},
        overrides={[f'stage5a_condition={condition}', f'experiment_seed={seed}']!r},
    )
assert list(config.application.editable.files) == ['Candidate.lean']
assert list(config.application.editable.folders) == []
assert int(config.loop.max_iterations) == 3
assert int(config.loop.n_workers_phase2) == 1
assert int(config.loop.produce_optimizer_in_phase2) == {1 if condition == 'evolved' else 0}
assert bool(config.loop.enable_resume) is False
assert config.resume_from is None and config.import_from is None
assert str(config.driver.model) == 'gpt-5.6-luna'
assert str(config.driver.reasoning_effort) == 'low'
assert str(config.driver.web_search) == 'disabled'
assert Path(config.optimizer.initial_guidance).is_dir()
assert len(_load_solver_worker_configs(config, search_root=Path({str(identity.root)!r}))) == 1
assert len(build_evaluation_plan(
    None, evaluation_config=config.evaluation, search_root=Path({str(identity.root)!r})
).steps) == 1
instantiate(config.optimizer.evaluation, _convert_='all')
for key in ('working_optimizer', 'solver_examples', 'solver_prefill', 'optimizer_examples', 'produced_optimizers'):
    instantiate(dict(config.loop.sampling[key]), _convert_='all')

wrapper_spec = importlib.util.spec_from_file_location(
    'econcslib_stage5a_wrapper', {str(SIDECAR_ROOT / 'scripts' / 'run_stage5a_eve.py')!r}
)
assert wrapper_spec is not None and wrapper_spec.loader is not None
wrapper = importlib.util.module_from_spec(wrapper_spec)
wrapper_spec.loader.exec_module(wrapper)
fake = SimpleNamespace(loop=SimpleNamespace(
    solver_pop=SimpleNamespace(_rng=random.Random()),
    optimizer_pop=SimpleNamespace(_rng=random.Random()),
    solver_workspace_builder=SimpleNamespace(_rng=random.Random()),
))
derived = wrapper.seed_factory(fake, {seed})
assert set(derived) == set(wrapper.STREAM_NAMES)
assert len(set(derived.values())) == 3
assert derived == wrapper.seed_factory(fake, {seed})
"""
        result = BASE._run_with_isolated_uv_cache(
            [
                uv,
                "run",
                "--offline",
                "--frozen",
                "--no-sync",
                "python",
                "-c",
                script,
            ],
            cwd=identity.root,
            env=env,
            timeout=60,
        )
        return result.returncode == 0


def _base_spec(spec: Stage5ASpec):
    return BASE.ExperimentSpec(
        cli_name=spec.cli_name,
        config_name=spec.config_name,
        seed_root=spec.seed_root,
        evaluator=spec.evaluator,
        evaluation_step=spec.evaluation_step,
        fixtures={"accepted": spec.accepted_fixture},
        requires_model_quota_ack=True,
        overlay_key=spec.overlay_key,
        loop_config_name="stage5a",
        driver_config_name="codex_luna_stage5a",
        evaluator_args=("--route", spec.route),
        stage4=False,
    )


def check(identity, spec: Stage5ASpec, *, condition: str, seed: int) -> int:
    verify_protocol_assets()
    verify_upstream_semantics(identity)
    verify_sidecar_assets(spec)
    try:
        toolchain = BASE._resolved_lean_toolchain_bin()
    except CheckError:
        toolchain = None
    tools = {
        "git": shutil.which("git") is not None,
        "uv": shutil.which("uv") is not None,
        "python3": shutil.which("python3") is not None,
        "lake": shutil.which("lake") is not None,
        "isolated solver Lean toolchain": (
            toolchain is not None
            and BASE._isolated_solver_lean_available(
                _base_spec(spec), toolchain_bin=toolchain
            )
        ),
        "codex executable": shutil.which("codex") is not None,
        "codex authentication": BASE._codex_auth_available(identity),
        "codex hook trust": BASE._codex_hook_trust_available(identity),
        "Stage 5A Hydra and seeded-wrapper probe": _dependency_probe(
            identity, spec, condition, seed
        ),
    }
    print(f"Stage 5A protocol: frozen ({_protocol_hash()})")
    print(f"EvE upstream: available ({identity.commit})")
    print(f"Cell: {spec.cli_name} / {condition} / {seed}")
    for name, available in tools.items():
        print(f"{name}: {'available' if available else 'unavailable'}")
    print("Model calls: 0; Codex credential values: never inspected or printed")
    return 0 if all(tools.values()) else 1


def dry_run(identity, spec: Stage5ASpec, *, condition: str, seed: int) -> int:
    protocol = verify_protocol_assets()
    verify_upstream_semantics(identity)
    verify_sidecar_assets(spec)
    preview = {
        "action": "dry-run-only",
        "protocol_id": PROTOCOL_ID,
        "protocol_sha256": _protocol_hash(),
        "protocol_status": protocol["status"],
        "calls_codex": False,
        "calls_model": False,
        "consumes_quota": False,
        "network": False,
        "writes_formal_run_results": False,
        "experiment": spec.cli_name,
        "route": spec.route,
        "condition": condition,
        "experiment_seed": seed,
        "iterations": ITERATIONS,
        "workers_per_iteration": 1,
        "maximum_model_sessions_for_cell": ITERATIONS,
        "resume": False,
        "import": False,
        "retry": False,
        "fresh_run_root_parent": str(RUNS_ROOT),
        "reads_stage4_run_roots": False,
        "provider_model_seed_controlled": False,
        "solver_prompt_bundle_sha256": prompt_bundle_sha256(spec),
    }
    print(json.dumps(preview, indent=2, sort_keys=True))
    return 0


def _new_run_root() -> Path:
    stamp = dt.datetime.now(dt.UTC).strftime("%Y%m%dT%H%M%S_%fZ")
    candidate = (RUNS_ROOT / stamp).resolve()
    if candidate.parent != RUNS_ROOT.resolve() or candidate.exists():
        raise CheckError("Stage 5A fresh run root is invalid or already exists")
    return candidate


def _materialize_route_overlay(run_root: Path, spec: Stage5ASpec) -> Path:
    root = run_root / "overlay"
    target = root / spec.overlay_key
    target.parent.mkdir(parents=True)
    shutil.copytree(OVERLAY_ROOT / spec.overlay_key, target)
    return root


def execute(
    identity,
    spec: Stage5ASpec,
    *,
    condition: str,
    seed: int,
    acknowledge_model_quota: bool,
) -> int:
    protocol = verify_protocol_assets()
    verify_upstream_semantics(identity)
    verify_sidecar_assets(spec)
    if not acknowledge_model_quota:
        raise CheckError("Stage 5A execution requires --acknowledge-model-quota")
    if not _dependency_probe(identity, spec, condition, seed):
        raise CheckError("Pinned Stage 5A dependencies or Hydra composition are unavailable")
    if shutil.which("codex") is None or not BASE._codex_auth_available(identity):
        raise CheckError("Codex executable or authentication is unavailable")
    toolchain = BASE._resolved_lean_toolchain_bin()
    if not BASE._isolated_solver_lean_available(
        _base_spec(spec), toolchain_bin=toolchain
    ):
        raise CheckError("Pinned Lean toolchain is unavailable in solver isolation")

    run_root = _new_run_root()
    run_root.mkdir(parents=True)
    runtime_overlay = _materialize_route_overlay(run_root, spec)
    if condition == "static":
        guidance_root = run_root / "static-empty-guidance"
        guidance_root.mkdir()
    else:
        guidance_root = runtime_overlay / spec.overlay_key / "initial_guidance"
    expected_guidance = protocol["initial_guidance_tree_hashes"][
        "static" if condition == "static" else f"{spec.cli_name}-fixed-and-evolved"
    ]
    if tree_sha256(guidance_root) != expected_guidance:
        raise CheckError("Stage 5A initial guidance tree hash mismatch")
    observation_path = run_root / "stage5a-guidance-lineage.jsonl"
    env = BASE._prepend_lean_toolchain_path(
        {
            **os.environ,
            "EVE_ECONCSLIB_ROOT": str(REPO_ROOT),
            "EVE_RUNTIME_OVERLAY_ROOT": str(runtime_overlay),
            "EVE_SIDECAR_RUN_ROOT": str(run_root),
            "EVE_STAGE5A_GUIDANCE_ROOT": str(guidance_root),
            "EVE_STAGE5A_OBSERVATION_PATH": str(observation_path),
            "PYTHONPATH": str(identity.root / "src"),
            "UV_CACHE_DIR": str(run_root / "uv-cache"),
        },
        toolchain,
    )
    command = [
        shutil.which("uv") or "uv",
        "run",
        "--offline",
        "--frozen",
        "--no-sync",
        "python",
        str(SIDECAR_ROOT / "scripts" / "run_stage5a_eve.py"),
        f"--config-dir={CONFIG_ROOT}",
        f"--config-name={spec.config_name}",
        f"stage5a_condition={condition}",
        f"experiment_seed={seed}",
    ]
    launch = {
        "schema_version": "1.0.0",
        "protocol_id": PROTOCOL_ID,
        "protocol_version": PROTOCOL_VERSION,
        "protocol_sha256": _protocol_hash(),
        "protocol_status_at_launch": protocol["status"],
        "run_root": str(run_root),
        "experiment": spec.cli_name,
        "route": spec.route,
        "condition": condition,
        "experiment_seed": seed,
        "model": "gpt-5.6-luna",
        "reasoning_effort": "low",
        "iterations": ITERATIONS,
        "workers_per_iteration": 1,
        "turn_budget": 8,
        "timeout_seconds": 900,
        "attempt_limit": 1,
        "retry": False,
        "resume": False,
        "import": False,
        "provider_model_seed_controlled": False,
        "initial_guidance_tree_sha256": tree_sha256(guidance_root),
        "solver_prompt_bundle_sha256": prompt_bundle_sha256(spec),
        "upstream_commit": identity.commit,
        "command": command,
        "status": "started",
        "exit_code": None,
    }
    launch_path = run_root / "stage5a-launch.json"
    launch_path.write_text(
        json.dumps(launch, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(f"Starting explicit Stage 5A EvE execution; artifacts: {run_root}")
    completed = subprocess.run(command, cwd=identity.root, env=env, check=False)
    launch["status"] = "completed" if completed.returncode == 0 else "failed"
    launch["exit_code"] = completed.returncode
    launch_path.write_text(
        json.dumps(launch, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    if completed.returncode == 0:
        audit = subprocess.run(
            [
                sys.executable,
                str(SIDECAR_ROOT / "scripts" / "audit_stage5a.py"),
                "--run-root",
                str(run_root),
                "--output",
                str(run_root / "stage5a-machine-audit.json"),
            ],
            cwd=REPO_ROOT,
            check=False,
        )
        if audit.returncode != 0:
            return audit.returncode
    return completed.returncode


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--eve-checkout", required=True, type=Path)
    parser.add_argument("--experiment", required=True, choices=sorted(SPECS))
    parser.add_argument("--protocol-id", required=True)
    parser.add_argument("--condition", required=True, choices=CONDITIONS)
    parser.add_argument("--experiment-seed", required=True, type=int)
    parser.add_argument("--acknowledge-model-quota", action="store_true")
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument("--check", action="store_true")
    actions.add_argument("--dry-run", action="store_true")
    actions.add_argument("--execute", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        validate_selection(
            protocol_id=args.protocol_id,
            condition=args.condition,
            experiment_seed=args.experiment_seed,
        )
        spec = SPECS[args.experiment]
        identity = BASE.verify_checkout(args.eve_checkout)
        if args.check:
            return check(
                identity, spec, condition=args.condition, seed=args.experiment_seed
            )
        if args.dry_run:
            return dry_run(
                identity, spec, condition=args.condition, seed=args.experiment_seed
            )
        if args.execute:
            return execute(
                identity,
                spec,
                condition=args.condition,
                seed=args.experiment_seed,
                acknowledge_model_quota=args.acknowledge_model_quota,
            )
        raise CheckError("No Stage 5A action selected")
    except (CheckError, OSError, subprocess.SubprocessError, json.JSONDecodeError) as exc:
        print(f"Stage 5A sidecar error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
