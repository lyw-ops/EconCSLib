#!/usr/bin/env python3
"""Safe entrypoint for frozen Stage 5B Sol REP-001; execution needs separate authorization."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import os
import re
import shutil
import sqlite3
import stat
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = SIDECAR_ROOT.parents[1]
CONFIG_ROOT = SIDECAR_ROOT / "configs" / "eve"
OVERLAY_ROOT = SIDECAR_ROOT / "overlay"
RUNS_ROOT = SIDECAR_ROOT / ".runtime" / "stage5b-sol-rep001-runs"
ATTEMPT_LEDGER_PATH = (
    SIDECAR_ROOT / ".runtime" / "stage5b-sol-rep001-attempt-ledger.sqlite3"
)
PROTOCOL_PATH = SIDECAR_ROOT / "stage5b_sol_rep001_protocol.json"
PROTOCOL_HASH_PATH = SIDECAR_ROOT / "stage5b_sol_rep001_protocol.sha256"
SEMANTICS_PATH = SIDECAR_ROOT / "stage5b_sol_rep001_upstream_semantics.json"
LEAN_ENVIRONMENT_PATH = SIDECAR_ROOT / "stage5b_sol_rep001_lean_environment.json"
PROTOCOL_ID = "EVE-STAGE5B-SOL-ENTRY-GAME-GUIDANCE-LIVENESS-REP-001"
PROTOCOL_VERSION = "1.0.0"
SOURCE_REPOSITORY = "https://github.com/lyw-ops/EconCSLib"
SOURCE_COMMIT = "b490317186ef435670c2eeb16050a214cdbf9fe5"
SOLVER_PYTHON = Path("/usr/bin/python3")
SOLVER_PYTHON_VERSION = "3.9.6"
SOLVER_PYTHON_EXECUTABLE = (
    "/Library/Developer/CommandLineTools/usr/bin/python3"
)
CONDITIONS = ("static", "fixed", "evolved")
SEEDS = (1729, 2718)
ITERATIONS = 3
LEAN_ENTRY_MODULE = (
    "EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete"
)
LEAN_BUILD_METADATA = ("lakefile.toml", "lake-manifest.json", "lean-toolchain")
_IMPORT_LINE = re.compile(r"^\s*import\s+(.+?)\s*(?:--.*)?$")


def _load_legacy():
    path = SIDECAR_ROOT / "scripts" / "run_stage5a.py"
    spec = importlib.util.spec_from_file_location("eve_stage5b_sol_rep001_core", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load frozen DEV-002 helper {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules["eve_stage5b_sol_rep001_core"] = module
    spec.loader.exec_module(module)
    return module


CORE = _load_legacy()
BASE = CORE.BASE
CheckError = CORE.CheckError
Stage5ASpec = CORE.Stage5ASpec
TASK_ROOT = SIDECAR_ROOT / "stage2_entry_game"
SPECS = {
    "entry-game-direct": Stage5ASpec(
        cli_name="entry-game-direct",
        route="direct",
        config_name="entry_game_direct_stage5b_sol_rep001",
        overlay_key="stage5b_sol_rep001_entry_game_direct",
        seed_root=TASK_ROOT / "direct" / "seed",
        accepted_fixture=TASK_ROOT / "direct" / "expected" / "Accepted.lean",
        evaluator=SIDECAR_ROOT / "scripts" / "evaluate_stage2_entry_game.py",
        evaluation_step=SIDECAR_ROOT / "scripts" / "evaluation_stage2_entry_direct.sh",
    ),
    "entry-game-transport": Stage5ASpec(
        cli_name="entry-game-transport",
        route="transport",
        config_name="entry_game_transport_stage5b_sol_rep001",
        overlay_key="stage5b_sol_rep001_entry_game_transport",
        seed_root=TASK_ROOT / "transport" / "seed",
        accepted_fixture=TASK_ROOT / "transport" / "expected" / "Accepted.lean",
        evaluator=SIDECAR_ROOT / "scripts" / "evaluate_stage2_entry_game.py",
        evaluation_step=SIDECAR_ROOT / "scripts" / "evaluation_stage2_entry_transport.sh",
    ),
}
for name, value in {
    "RUNS_ROOT": RUNS_ROOT,
    "ATTEMPT_LEDGER_PATH": ATTEMPT_LEDGER_PATH,
    "PROTOCOL_PATH": PROTOCOL_PATH,
    "PROTOCOL_HASH_PATH": PROTOCOL_HASH_PATH,
    "SEMANTICS_PATH": SEMANTICS_PATH,
    "LEAN_ENVIRONMENT_PATH": LEAN_ENVIRONMENT_PATH,
    "PROTOCOL_ID": PROTOCOL_ID,
    "PROTOCOL_VERSION": PROTOCOL_VERSION,
    "SPECS": SPECS,
}.items():
    setattr(CORE, name, value)

sha256 = CORE.sha256
tree_sha256 = CORE.tree_sha256
prompt_bundle_sha256 = CORE.prompt_bundle_sha256
_is_relative_to = CORE._is_relative_to


def _run_git(root: Path, *args: str, text: bool = True):
    completed = subprocess.run(
        ["git", *args],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=text,
        check=False,
    )
    if completed.returncode != 0:
        raise CheckError(f"Git verification failed: {' '.join(args)}")
    return completed.stdout


def _source_blob(relative: str) -> bytes:
    return _run_git(
        REPO_ROOT, "show", f"{SOURCE_COMMIT}:{relative}", text=False
    )


def _source_module_blob(module: str) -> tuple[str, bytes]:
    relative = Path(*module.split(".")).with_suffix(".lean").as_posix()
    return relative, _source_blob(relative)


def committed_lean_import_closure(entry_modules: tuple[str, ...]) -> dict[str, str]:
    """Hash the complete local Lean closure from the pinned committed tree."""
    pending = list(entry_modules)
    seen: set[str] = set()
    closure: dict[str, str] = {}
    while pending:
        module = pending.pop()
        if module in seen or not module.startswith("EconCSLib"):
            continue
        seen.add(module)
        relative, payload = _source_module_blob(module)
        closure[relative] = hashlib.sha256(payload).hexdigest()
        for line in payload.decode("utf-8").splitlines():
            match = _IMPORT_LINE.match(line)
            if match is None:
                continue
            for imported in match.group(1).split():
                if imported.startswith("EconCSLib") and imported not in seen:
                    pending.append(imported)
    return dict(sorted(closure.items()))


def load_lean_environment(protocol: dict[str, Any]) -> dict[str, Any]:
    record = protocol.get("lean_environment_manifest")
    expected = {
        "path": "experiments/eve/stage5b_sol_rep001_lean_environment.json",
        "sha256": sha256(LEAN_ENVIRONMENT_PATH),
    }
    if record != expected:
        raise CheckError("Sol REP-001 Lean environment manifest hash drifted")
    try:
        value = json.loads(LEAN_ENVIRONMENT_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CheckError("Sol REP-001 Lean environment manifest is invalid") from exc
    if not isinstance(value, dict):
        raise CheckError("Sol REP-001 Lean environment manifest is not an object")
    return value


def verify_manifest_against_source_commit(environment: dict[str, Any]) -> None:
    if environment.get("source_repository") != SOURCE_REPOSITORY:
        raise CheckError("Sol REP-001 Lean source repository drifted")
    if environment.get("source_commit") != SOURCE_COMMIT:
        raise CheckError("Sol REP-001 Lean source commit drifted")
    if environment.get("entry_modules") != [LEAN_ENTRY_MODULE]:
        raise CheckError("Sol REP-001 Lean entry modules drifted")
    actual_closure = committed_lean_import_closure((LEAN_ENTRY_MODULE,))
    if environment.get("local_import_closure") != actual_closure:
        raise CheckError("Sol REP-001 committed Lean import closure drifted")
    metadata = {
        relative: hashlib.sha256(_source_blob(relative)).hexdigest()
        for relative in LEAN_BUILD_METADATA
    }
    if environment.get("build_metadata") != metadata:
        raise CheckError("Sol REP-001 committed Lake metadata drifted")
    manifest = json.loads(_source_blob("lake-manifest.json").decode("utf-8"))
    packages = {
        str(item["name"]): str(item["rev"]) for item in manifest.get("packages", [])
    }
    if environment.get("dependency_checkouts") != packages:
        raise CheckError("Sol REP-001 dependency revisions drifted")


def _normalize_remote(value: str) -> str:
    return value.removesuffix(".git").removesuffix("/")


def verify_clean_lean_checkout(lean_root: Path, environment: dict[str, Any]) -> Path:
    root = lean_root.resolve()
    if not (root / ".git").exists() or not (root / "lakefile.toml").is_file():
        raise CheckError("Sol REP-001 clean Lean checkout is unavailable")
    head = str(_run_git(root, "rev-parse", "HEAD")).strip()
    if head != SOURCE_COMMIT:
        raise CheckError("Sol REP-001 clean Lean checkout is at the wrong commit")
    status = str(_run_git(root, "status", "--porcelain", "--untracked-files=all"))
    if status.strip():
        raise CheckError("Sol REP-001 Lean checkout is not tracked-clean")
    remotes = str(_run_git(root, "remote", "-v"))
    if _normalize_remote(SOURCE_REPOSITORY) not in {
        _normalize_remote(line.split()[1])
        for line in remotes.splitlines()
        if len(line.split()) >= 2
    }:
        raise CheckError("Sol REP-001 Lean checkout lacks the frozen repository remote")
    for relative, expected in environment["local_import_closure"].items():
        path = root / relative
        if not path.is_file() or sha256(path) != expected:
            raise CheckError(f"Sol REP-001 clean Lean source drifted: {relative}")
    for relative, expected in environment["build_metadata"].items():
        path = root / relative
        if not path.is_file() or sha256(path) != expected:
            raise CheckError(f"Sol REP-001 clean build metadata drifted: {relative}")
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    packages_root = root / str(manifest.get("packagesDir", ".lake/packages"))
    for name, revision in sorted(environment["dependency_checkouts"].items()):
        checkout = packages_root / name
        if not checkout.is_dir():
            raise CheckError(f"Sol REP-001 dependency checkout is missing: {name}")
        if str(_run_git(checkout, "rev-parse", "HEAD")).strip() != revision:
            raise CheckError(f"Sol REP-001 dependency commit drifted: {name}")
        dirty = str(_run_git(checkout, "status", "--porcelain", "--untracked-files=no"))
        if dirty.strip():
            raise CheckError(f"Sol REP-001 dependency checkout is dirty: {name}")
    return root


def _protocol_hash() -> str:
    record = PROTOCOL_HASH_PATH.read_text(encoding="utf-8").split()
    expected_path = "experiments/eve/stage5b_sol_rep001_protocol.json"
    if len(record) != 2 or record[1] != expected_path:
        raise CheckError("Sol REP-001 detached protocol hash record is invalid")
    actual = sha256(PROTOCOL_PATH)
    if record[0] != actual:
        raise CheckError("Sol REP-001 protocol hash mismatch")
    return actual


CORE._protocol_hash = _protocol_hash


def verify_protocol_assets(lean_checkout: Path | None = None) -> dict[str, Any]:
    try:
        protocol = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CheckError("Sol REP-001 protocol is missing or invalid") from exc
    _protocol_hash()
    if protocol.get("id") != PROTOCOL_ID or protocol.get("version") != PROTOCOL_VERSION:
        raise CheckError("Sol REP-001 protocol identity or version mismatch")
    if protocol.get("status") != "FROZEN_NOT_YET_EXECUTED":
        raise CheckError("Sol REP-001 protocol is not frozen and unexecuted")
    for section in ("frozen_artifacts", "protected_historical_evidence"):
        records = protocol.get(section)
        if not isinstance(records, dict) or not records:
            raise CheckError(f"Sol REP-001 protocol has no {section}")
        for relative, expected in records.items():
            artifact = (REPO_ROOT / str(relative)).resolve()
            if not _is_relative_to(artifact, REPO_ROOT.resolve()):
                raise CheckError("Sol REP-001 frozen artifact escaped the repository")
            if not artifact.is_file() or sha256(artifact) != expected:
                raise CheckError(f"Sol REP-001 frozen artifact mismatch: {relative}")
    prompt_hashes = {
        spec.route: prompt_bundle_sha256(spec) for spec in SPECS.values()
    }
    if protocol.get("solver_prompt_bundle_hashes") != prompt_hashes:
        raise CheckError("Sol REP-001 solver prompt bundle hash mismatch")
    if protocol.get("edit_surfaces") != {
        "solver_candidate": "solver/Candidate.lean",
        "failure_derived_guidance": "guidance/docs/learned.md",
        "guidance_requires_prior_recorded_failure": True,
        "all_other_paths_editable": False,
    }:
        raise CheckError("Sol REP-001 edit surfaces are not exact")
    contract = protocol.get("checker_evidence_contract", {})
    if not all(
        contract.get(key) is True
        for key in (
            "at_least_one_valid_event_per_rollout",
            "final_event_matches_final_candidate",
            "missing_empty_malformed_or_mismatched_fails",
            "failed_event_alone_cannot_establish_liveness",
        )
    ):
        raise CheckError("Sol REP-001 checker evidence contract is not fail closed")
    environment = load_lean_environment(protocol)
    verify_manifest_against_source_commit(environment)
    if lean_checkout is not None:
        verify_clean_lean_checkout(lean_checkout, environment)
    return protocol


def verify_upstream_semantics(identity) -> None:
    CORE.verify_upstream_semantics(identity)


def _required_paths(spec: Stage5ASpec) -> tuple[Path, ...]:
    route_root = OVERLAY_ROOT / spec.overlay_key
    paths = (
        CONFIG_ROOT / "runtime" / "sidecar.yaml",
        CONFIG_ROOT / "loop" / "stage5a.yaml",
        CONFIG_ROOT / "driver" / "codex_sol_stage5b.yaml",
        CONFIG_ROOT / "logger" / "local.yaml",
        CONFIG_ROOT / f"{spec.config_name}.yaml",
        CONFIG_ROOT / "application" / f"entry_game_{spec.route}.yaml",
        CONFIG_ROOT / "evaluation" / f"entry_game_{spec.route}.yaml",
        CONFIG_ROOT / "optimizer" / f"entry_game_{spec.route}_stage5b_sol_rep001.yaml",
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
        SIDECAR_ROOT / "scripts" / "run_stage5b_sol_rep001_eve.py",
        SIDECAR_ROOT / "scripts" / "audit_stage5b_sol_rep001.py",
        SIDECAR_ROOT / "scripts" / "verify_stage5b_sol_rep001_protocol.py",
        PROTOCOL_PATH,
        PROTOCOL_HASH_PATH,
        SEMANTICS_PATH,
        LEAN_ENVIRONMENT_PATH,
    )
    if spec.route == "transport":
        return paths + (route_root / "immutable" / "TRANSPORT_CHECKPOINTS.md",)
    return paths


def verify_sidecar_assets(spec: Stage5ASpec, lean_root: Path) -> None:
    missing = [
        path.relative_to(REPO_ROOT).as_posix()
        for path in _required_paths(spec)
        if not path.is_file()
    ]
    if missing:
        raise CheckError("Missing Sol REP-001 assets: " + ", ".join(missing))
    case_path = lean_root / "experiments/eve/stage2_entry_game" / spec.route / "case.json"
    case = json.loads(case_path.read_text(encoding="utf-8"))
    if case.get("editable_files") != ["Candidate.lean"]:
        raise CheckError("Sol REP-001 solver file boundary drifted")
    if case.get("editable_folders") != []:
        raise CheckError("Sol REP-001 solver folder boundary drifted")


def validate_selection(*, protocol_id: str, condition: str, experiment_seed: int) -> None:
    if protocol_id != PROTOCOL_ID:
        raise CheckError("Sol REP-001 protocol id mismatch")
    if condition not in CONDITIONS:
        raise CheckError("Sol REP-001 condition is not frozen")
    if experiment_seed not in SEEDS:
        raise CheckError("Sol REP-001 experiment seed is not frozen")


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
        driver_config_name="codex_sol_stage5b",
        evaluator_args=("--route", spec.route),
        stage4=False,
    )


def _dependency_probe(identity, spec: Stage5ASpec, condition: str, seed: int, lean_root: Path) -> bool:
    uv = shutil.which("uv")
    if uv is None or not (identity.root / ".venv" / "bin" / "python").is_file():
        return False
    with tempfile.TemporaryDirectory(prefix="econcslib-stage5b-sol-rep001-probe-") as raw:
        temp_root = Path(raw)
        guidance = (
            temp_root / "empty-guidance"
            if condition == "static"
            else OVERLAY_ROOT / spec.overlay_key / "initial_guidance"
        )
        guidance.mkdir(parents=True, exist_ok=True)
        env = {
            **os.environ,
            "EVE_ECONCSLIB_ROOT": str(lean_root),
            "EVE_RUNTIME_OVERLAY_ROOT": str(OVERLAY_ROOT),
            "EVE_SIDECAR_RUN_ROOT": str(temp_root / "run"),
            "EVE_STAGE5B_GUIDANCE_ROOT": str(guidance),
            "EVE_STAGE5B_OBSERVATION_PATH": str(temp_root / "events.jsonl"),
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
assert str(config.driver.model) == 'gpt-5.6-sol'
assert str(config.driver.reasoning_effort) == 'low'
assert str(config.driver.web_search) == 'disabled'
assert Path(config.optimizer.initial_guidance).is_dir()
assert len(_load_solver_worker_configs(config, search_root=Path({str(identity.root)!r}))) == 1
assert len(build_evaluation_plan(None, evaluation_config=config.evaluation, search_root=Path({str(identity.root)!r})).steps) == 1
instantiate(config.optimizer.evaluation, _convert_='all')
for key in ('working_optimizer', 'solver_examples', 'solver_prefill', 'optimizer_examples', 'produced_optimizers'):
    instantiate(dict(config.loop.sampling[key]), _convert_='all')
wrapper_spec = importlib.util.spec_from_file_location('econcslib_stage5b_sol_rep001_wrapper', {str(SIDECAR_ROOT / 'scripts' / 'run_stage5b_sol_rep001_eve.py')!r})
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
            [uv, "run", "--offline", "--frozen", "--no-sync", "python", "-c", script],
            cwd=identity.root,
            env=env,
            timeout=60,
        )
        return result.returncode == 0


def _build_frozen_lean_entry(protocol: dict[str, Any], lean_root: Path) -> None:
    target = load_lean_environment(protocol).get("prelaunch_build_target")
    if target != LEAN_ENTRY_MODULE:
        raise CheckError("Sol REP-001 prelaunch Lean target drifted")
    completed = subprocess.run(
        ["lake", "build", target],
        cwd=lean_root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        detail = (completed.stdout + completed.stderr)[-4000:]
        raise CheckError(f"Sol REP-001 clean Lean entry did not build:\n{detail}")


def _canonical_sha256(payload: object) -> str:
    return hashlib.sha256(
        json.dumps(
            payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False
        ).encode("utf-8")
    ).hexdigest()


def _is_sqlite_sidecar(path: Path) -> bool:
    return path.name.endswith(("-wal", "-shm", "-journal"))


def _is_sqlite_database(path: Path) -> bool:
    return path.suffix.lower() in {".db", ".sqlite", ".sqlite3"}


def _sqlite_value(value: object) -> object:
    if isinstance(value, bytes):
        return {"blob_hex": value.hex()}
    if value is None or isinstance(value, (str, int, float)):
        return value
    return {"repr": repr(value)}


def _sqlite_logical_payload(path: Path) -> dict[str, object]:
    """Read stable committed SQLite contents without hashing WAL layout."""
    if not path.exists():
        return {"exists": False}
    if not path.is_file() or path.is_symlink():
        raise CheckError(f"SQLite snapshot target is not a regular file: {path}")
    uri = path.resolve().as_uri() + "?mode=ro"
    connection = sqlite3.connect(uri, uri=True, timeout=1.0)
    try:
        connection.execute("PRAGMA query_only = ON")
        connection.execute("BEGIN")
        schema_rows = connection.execute(
            "SELECT type, name, tbl_name, sql FROM sqlite_master "
            "WHERE name NOT LIKE 'sqlite_%' ORDER BY type, name"
        ).fetchall()
        tables: list[dict[str, object]] = []
        for object_type, name, table_name, sql in schema_rows:
            if object_type != "table":
                continue
            quoted = '"' + str(name).replace('"', '""') + '"'
            rows = [
                [_sqlite_value(value) for value in row]
                for row in connection.execute(f"SELECT * FROM {quoted}").fetchall()
            ]
            rows.sort(
                key=lambda row: json.dumps(
                    row, sort_keys=True, separators=(",", ":"), ensure_ascii=False
                )
            )
            tables.append({"name": name, "rows": rows})
        connection.execute("COMMIT")
    finally:
        connection.close()
    return {
        "exists": True,
        "schema": [
            {
                "type": row[0],
                "name": row[1],
                "table": row[2],
                "sql": row[3],
            }
            for row in schema_rows
        ],
        "tables": tables,
    }


def _sqlite_logical_sha256(path: Path) -> str:
    return _canonical_sha256(_sqlite_logical_payload(path))


def _projected_filesystem_sha256(path: Path) -> str:
    """Digest durable contents while normalizing SQLite physical sidecars."""
    if not path.exists() and not path.is_symlink():
        return _canonical_sha256({"exists": False})
    candidates = [path]
    if path.is_dir() and not path.is_symlink():
        candidates.extend(sorted(path.rglob("*")))
    entries: list[dict[str, object]] = []
    for candidate in candidates:
        if _is_sqlite_sidecar(candidate):
            continue
        relative = "." if candidate == path else candidate.relative_to(path).as_posix()
        metadata = candidate.lstat()
        entry: dict[str, object] = {
            "relative": relative,
            "mode": stat.S_IMODE(metadata.st_mode),
        }
        if candidate.is_symlink():
            entry.update(kind="symlink", target=os.readlink(candidate))
        elif candidate.is_dir():
            entry["kind"] = "directory"
        elif candidate.is_file():
            entry["kind"] = "sqlite" if _is_sqlite_database(candidate) else "file"
            entry["content_sha256"] = (
                _sqlite_logical_sha256(candidate)
                if _is_sqlite_database(candidate)
                else sha256(candidate)
            )
        else:
            entry.update(kind="other", size=metadata.st_size)
        entries.append(entry)
    return _canonical_sha256({"exists": True, "entries": entries})


def _execution_state_snapshot(runs: Path, ledger: Path) -> dict[str, object]:
    return {
        "schema_version": "1.0.0",
        "runs_projection_sha256": _projected_filesystem_sha256(runs),
        "attempt_ledger_logical_sha256": _sqlite_logical_sha256(ledger),
    }


def _historical_state_snapshot() -> dict[str, object]:
    runtime = SIDECAR_ROOT / ".runtime"
    return {
        generation: _execution_state_snapshot(
            runtime / f"stage5a-{generation}-runs",
            runtime / f"stage5a-{generation}-attempt-ledger.sqlite3",
        )
        for generation in ("dev002", "dev003")
    }


def _wait_for_quiescent_snapshot(
    snapshotter,
    *,
    label: str,
    stable_samples: int = 3,
    poll_seconds: float = 0.05,
    timeout_seconds: float = 5.0,
) -> tuple[object, dict[str, object]]:
    """Require repeated identical logical snapshots before crossing a boundary."""
    if stable_samples < 2 or poll_seconds < 0 or timeout_seconds <= 0:
        raise ValueError("invalid quiescence parameters")
    deadline = time.monotonic() + timeout_seconds
    previous: object = object()
    stable = 0
    samples = 0
    last_error: Exception | None = None
    while time.monotonic() <= deadline:
        samples += 1
        try:
            current = snapshotter()
        except (OSError, sqlite3.Error) as exc:
            last_error = exc
            stable = 0
        else:
            last_error = None
            if current == previous:
                stable += 1
            else:
                previous = current
                stable = 1
            if stable >= stable_samples:
                return current, {
                    "label": label,
                    "stable_samples_required": stable_samples,
                    "samples_observed": samples,
                    "poll_seconds": poll_seconds,
                    "timeout_seconds": timeout_seconds,
                }
        if poll_seconds:
            time.sleep(poll_seconds)
    detail = f": {last_error}" if last_error is not None else ""
    raise CheckError(f"{label} did not become logically quiescent{detail}")


def safe_preflight(spec: Stage5ASpec, lean_root: Path, toolchain: Path) -> dict[str, Any]:
    """Run the immutable checker with the exact solver Python before formal state."""
    formal_before, formal_before_barrier = _wait_for_quiescent_snapshot(
        lambda: _execution_state_snapshot(RUNS_ROOT, ATTEMPT_LEDGER_PATH),
        label="Sol REP-001 formal state before preflight",
    )
    historical_before, historical_before_barrier = _wait_for_quiescent_snapshot(
        _historical_state_snapshot,
        label="DEV-002 and DEV-003 historical state before preflight",
    )
    version = subprocess.run(
        [str(SOLVER_PYTHON), "-c", "import platform,sys; print(platform.python_version()); print(sys.executable)"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if version.returncode != 0 or version.stdout.splitlines() != [
        SOLVER_PYTHON_VERSION,
        SOLVER_PYTHON_EXECUTABLE,
    ]:
        raise CheckError("exact isolated solver Python 3.9.6 is unavailable")
    checker_source = OVERLAY_ROOT / spec.overlay_key / "immutable" / "STAGE5A_LEAN_CHECK.py"
    temp_path: Path | None = None
    with tempfile.TemporaryDirectory(prefix="econcslib-stage5b-sol-rep001-preflight-") as raw:
        workspace = Path(raw).resolve()
        temp_path = workspace
        if _is_relative_to(workspace, SIDECAR_ROOT.resolve()):
            raise CheckError("Sol REP-001 preflight workspace is not disposable")
        (workspace / "solver").mkdir()
        candidate = workspace / "solver" / "Candidate.lean"
        candidate.write_text(
            "import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete\n"
            "def stage5aDev003Preflight : Nat := deliberatelyMissingIdentifier\n",
            encoding="utf-8",
        )
        checker = workspace / "STAGE5A_LEAN_CHECK.py"
        shutil.copy2(checker_source, checker)
        env = BASE._prepend_lean_toolchain_path(
            {**os.environ, "EVE_ECONCSLIB_ROOT": str(lean_root)}, toolchain
        )
        completed = subprocess.run(
            [str(SOLVER_PYTHON), str(checker)],
            cwd=workspace,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if completed.returncode == 0:
            raise CheckError("Sol REP-001 preflight did not exercise a real Lean failure")
        events_path = workspace / ".scaling_evolve" / "stage5a-lean-checks.jsonl"
        if not events_path.is_file():
            raise CheckError("Sol REP-001 preflight checker recorded no event")
        lines = [line for line in events_path.read_text(encoding="utf-8").splitlines() if line]
        if len(lines) != 1:
            raise CheckError("Sol REP-001 preflight checker event count is not one")
        try:
            event = json.loads(lines[0])
        except json.JSONDecodeError as exc:
            raise CheckError("Sol REP-001 preflight checker event is malformed") from exc
        expected = {
            "schema_version": "2.0.0",
            "sequence": 1,
            "previous_event_sha256": None,
            "python_invocation": str(SOLVER_PYTHON),
            "python_executable": SOLVER_PYTHON_EXECUTABLE,
            "python_version": SOLVER_PYTHON_VERSION,
            "command": ["lake", "env", "lean", "solver/Candidate.lean"],
            "checker_sha256": sha256(checker),
            "candidate_sha256": sha256(candidate),
            "exit_code": completed.returncode,
            "failed": True,
            "stdout_sha256": hashlib.sha256(completed.stdout).hexdigest(),
            "stderr_sha256": hashlib.sha256(completed.stderr).hexdigest(),
            "stdout_bytes": len(completed.stdout),
            "stderr_bytes": len(completed.stderr),
        }
        for key, value in expected.items():
            if event.get(key) != value:
                raise CheckError(f"Sol REP-001 preflight event mismatch: {key}")
        payload = {key: value for key, value in event.items() if key != "event_sha256"}
        digest = hashlib.sha256(
            json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        ).hexdigest()
        if event.get("event_sha256") != digest:
            raise CheckError("Sol REP-001 preflight event hash is invalid")
        report = {
            "schema_version": "2.0.0",
            "route": spec.route,
            "solver_python_invocation": str(SOLVER_PYTHON),
            "solver_python_executable": SOLVER_PYTHON_EXECUTABLE,
            "solver_python_version": SOLVER_PYTHON_VERSION,
            "checker_sha256": sha256(checker),
            "candidate_sha256": sha256(candidate),
            "lean_exit_code": completed.returncode,
            "lean_stdout_sha256": hashlib.sha256(completed.stdout).hexdigest(),
            "lean_stderr_sha256": hashlib.sha256(completed.stderr).hexdigest(),
            "lean_stdout_bytes": len(completed.stdout),
            "lean_stderr_bytes": len(completed.stderr),
            "recorded_event_sha256": event["event_sha256"],
            "model_calls": 0,
            "sol_quota_consumed": 0,
            "formal_run_root_written": False,
            "formal_attempt_ledger_written": False,
            "historical_execution_state_inherited_or_written": False,
            "snapshot_contract": "durable-files-and-sqlite-logical-content-v1",
        }
    if temp_path is None or temp_path.exists():
        raise CheckError("Sol REP-001 disposable preflight workspace was not removed")
    formal_after, formal_after_barrier = _wait_for_quiescent_snapshot(
        lambda: _execution_state_snapshot(RUNS_ROOT, ATTEMPT_LEDGER_PATH),
        label="Sol REP-001 formal state after preflight",
    )
    if formal_before != formal_after:
        raise CheckError("Sol REP-001 preflight changed projected formal execution state")
    historical_after, historical_after_barrier = _wait_for_quiescent_snapshot(
        _historical_state_snapshot,
        label="DEV-002 and DEV-003 historical state after preflight",
    )
    if historical_before != historical_after:
        raise CheckError("Sol REP-001 preflight changed projected historical state")
    report["disposable_workspace_removed"] = True
    report["quiescence_barrier_passed"] = True
    report["formal_state_projection_unchanged"] = True
    report["historical_state_projection_unchanged"] = True
    report["formal_state_before_sha256"] = _canonical_sha256(formal_before)
    report["formal_state_after_sha256"] = _canonical_sha256(formal_after)
    report["historical_state_before_sha256"] = _canonical_sha256(historical_before)
    report["historical_state_after_sha256"] = _canonical_sha256(historical_after)
    report["quiescence"] = {
        "formal_before": formal_before_barrier,
        "formal_after": formal_after_barrier,
        "historical_before": historical_before_barrier,
        "historical_after": historical_after_barrier,
    }
    return report


def check(identity, spec: Stage5ASpec, *, condition: str, seed: int, lean_checkout: Path) -> int:
    protocol = verify_protocol_assets(lean_checkout)
    environment = load_lean_environment(protocol)
    lean_root = verify_clean_lean_checkout(lean_checkout, environment)
    verify_upstream_semantics(identity)
    verify_sidecar_assets(spec, lean_root)
    toolchain = BASE._resolved_lean_toolchain_bin()
    _build_frozen_lean_entry(protocol, lean_root)
    preflight = safe_preflight(spec, lean_root, toolchain)
    tools = {
        "git": shutil.which("git") is not None,
        "uv": shutil.which("uv") is not None,
        "exact isolated solver Python 3.9.6": preflight["solver_python_version"] == "3.9.6",
        "clean committed Lean source": True,
        "isolated solver Lean toolchain": preflight["recorded_event_sha256"] is not None,
        "Codex executable": shutil.which("codex") is not None,
        "Codex authentication": BASE._codex_auth_available(identity),
        "Codex hook trust": BASE._codex_hook_trust_available(identity),
        "Sol REP-001 Hydra and wrapper probe": _dependency_probe(
            identity, spec, condition, seed, lean_root
        ),
        "real immutable-checker preflight": preflight["recorded_event_sha256"] is not None,
    }
    print(f"Stage 5B Sol REP-001 protocol: frozen ({_protocol_hash()})")
    print(f"Lean source: clean {SOURCE_COMMIT}")
    print(f"Cell: {spec.cli_name} / {condition} / {seed}")
    for name, available in tools.items():
        print(f"{name}: {'available' if available else 'unavailable'}")
    print(json.dumps({"safe_preflight": preflight}, sort_keys=True))
    print("Model calls: 0; formal run roots/ledger writes: 0; historical state reuse: 0")
    return 0 if all(tools.values()) else 1


def dry_run(identity, spec: Stage5ASpec, *, condition: str, seed: int, lean_checkout: Path) -> int:
    protocol = verify_protocol_assets(lean_checkout)
    verify_upstream_semantics(identity)
    lean_root = verify_clean_lean_checkout(
        lean_checkout, load_lean_environment(protocol)
    )
    verify_sidecar_assets(spec, lean_root)
    preview = {
        "action": "dry-run-only",
        "protocol_id": PROTOCOL_ID,
        "protocol_sha256": _protocol_hash(),
        "protocol_status": protocol["status"],
        "calls_codex": False,
        "calls_model": False,
        "consumes_quota": False,
        "writes_formal_run_results": False,
        "experiment": spec.cli_name,
        "condition": condition,
        "experiment_seed": seed,
        "clean_lean_source_commit": SOURCE_COMMIT,
        "exact_solver_python": str(SOLVER_PYTHON),
        "iterations": ITERATIONS,
        "fresh_run_root_parent": str(RUNS_ROOT),
        "fresh_attempt_ledger": str(ATTEMPT_LEDGER_PATH),
        "attempt_ledger_touched": False,
        "inherits_or_writes_historical_execution_state": False,
        "retry": False,
        "resume": False,
        "import": False,
        "provider_model_seed_controlled": False,
        "solver_prompt_bundle_sha256": prompt_bundle_sha256(spec),
    }
    print(json.dumps(preview, indent=2, sort_keys=True))
    return 0


def _new_run_root() -> Path:
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ")
    candidate = (RUNS_ROOT / stamp).resolve()
    if candidate.parent != RUNS_ROOT.resolve() or candidate.exists():
        raise CheckError("Sol REP-001 fresh run root is invalid or already exists")
    return candidate


def reserve_attempt(
    protocol: dict[str, Any],
    *,
    task: str,
    condition: str,
    seed: int,
    run_root: Path,
    ledger_path: Path = ATTEMPT_LEDGER_PATH,
) -> int:
    return CORE.reserve_attempt(
        protocol,
        task=task,
        condition=condition,
        seed=seed,
        run_root=run_root,
        ledger_path=ledger_path,
    )


def finish_attempt(
    ordinal: int,
    *,
    status: str,
    exit_code: int,
    ledger_path: Path = ATTEMPT_LEDGER_PATH,
) -> None:
    CORE.finish_attempt(
        ordinal,
        status=status,
        exit_code=exit_code,
        ledger_path=ledger_path,
    )


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
    lean_checkout: Path,
    acknowledge_model_quota: bool,
) -> int:
    protocol = verify_protocol_assets(lean_checkout)
    lean_root = verify_clean_lean_checkout(
        lean_checkout, load_lean_environment(protocol)
    )
    verify_upstream_semantics(identity)
    verify_sidecar_assets(spec, lean_root)
    if not acknowledge_model_quota:
        raise CheckError("Sol REP-001 execution requires --acknowledge-model-quota")
    if not _dependency_probe(identity, spec, condition, seed, lean_root):
        raise CheckError("Sol REP-001 dependencies or Hydra composition are unavailable")
    if shutil.which("codex") is None or not BASE._codex_auth_available(identity):
        raise CheckError("Codex executable or authentication is unavailable")
    toolchain = BASE._resolved_lean_toolchain_bin()
    _build_frozen_lean_entry(protocol, lean_root)
    preflight = safe_preflight(spec, lean_root, toolchain)
    run_root = _new_run_root()
    ordinal = reserve_attempt(
        protocol,
        task=spec.cli_name,
        condition=condition,
        seed=seed,
        run_root=run_root,
    )
    try:
        run_root.mkdir(parents=True)
    except Exception:
        finish_attempt(ordinal, status="failed", exit_code=-1)
        raise
    runtime_overlay = _materialize_route_overlay(run_root, spec)
    if condition == "static":
        guidance_root = run_root / "static-empty-guidance"
        guidance_root.mkdir()
    else:
        guidance_root = runtime_overlay / spec.overlay_key / "initial_guidance"
    guidance_key = (
        "static" if condition == "static" else f"{spec.cli_name}-fixed-and-evolved"
    )
    if tree_sha256(guidance_root) != protocol["initial_guidance_tree_hashes"][guidance_key]:
        raise CheckError("Sol REP-001 initial guidance tree hash mismatch")
    observation_path = run_root / "stage5a-guidance-lineage.jsonl"
    env = BASE._prepend_lean_toolchain_path(
        {
            **os.environ,
            "EVE_ECONCSLIB_ROOT": str(lean_root),
            "EVE_RUNTIME_OVERLAY_ROOT": str(runtime_overlay),
            "EVE_SIDECAR_RUN_ROOT": str(run_root),
            "EVE_STAGE5B_GUIDANCE_ROOT": str(guidance_root),
            "EVE_STAGE5B_OBSERVATION_PATH": str(observation_path),
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
        str(SIDECAR_ROOT / "scripts" / "run_stage5b_sol_rep001_eve.py"),
        f"--config-dir={CONFIG_ROOT}",
        f"--config-name={spec.config_name}",
        f"stage5a_condition={condition}",
        f"experiment_seed={seed}",
    ]
    launch = {
        "schema_version": "2.0.0",
        "protocol_id": PROTOCOL_ID,
        "protocol_version": PROTOCOL_VERSION,
        "protocol_sha256": _protocol_hash(),
        "protocol_status_at_launch": protocol["status"],
        "run_root": str(run_root),
        "experiment": spec.cli_name,
        "route": spec.route,
        "condition": condition,
        "experiment_seed": seed,
        "model": "gpt-5.6-sol",
        "reasoning_effort": "low",
        "iterations": ITERATIONS,
        "workers_per_iteration": 1,
        "turn_budget": 8,
        "timeout_seconds": 900,
        "attempt_limit": 1,
        "matrix_ordinal": ordinal,
        "attempt_ledger": str(ATTEMPT_LEDGER_PATH),
        "attempt_reserved_before_model_access": True,
        "retry": False,
        "resume": False,
        "import": False,
        "provider_model_seed_controlled": False,
        "clean_lean_source_commit": SOURCE_COMMIT,
        "safe_preflight": preflight,
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
    completed = subprocess.run(command, cwd=identity.root, env=env, check=False)
    launch["status"] = "completed" if completed.returncode == 0 else "failed"
    launch["exit_code"] = completed.returncode
    launch_path.write_text(
        json.dumps(launch, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    finish_attempt(
        ordinal,
        status="completed" if completed.returncode == 0 else "failed",
        exit_code=completed.returncode,
    )
    if completed.returncode == 0:
        audit = subprocess.run(
            [
                sys.executable,
                str(SIDECAR_ROOT / "scripts" / "audit_stage5b_sol_rep001.py"),
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
    parser.add_argument("--lean-checkout", required=True, type=Path)
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
                identity,
                spec,
                condition=args.condition,
                seed=args.experiment_seed,
                lean_checkout=args.lean_checkout,
            )
        if args.dry_run:
            return dry_run(
                identity,
                spec,
                condition=args.condition,
                seed=args.experiment_seed,
                lean_checkout=args.lean_checkout,
            )
        if args.execute:
            return execute(
                identity,
                spec,
                condition=args.condition,
                seed=args.experiment_seed,
                lean_checkout=args.lean_checkout,
                acknowledge_model_quota=args.acknowledge_model_quota,
            )
        raise CheckError("No Sol REP-001 action selected")
    except (CheckError, OSError, subprocess.SubprocessError, json.JSONDecodeError) as exc:
        print(f"Stage 5B Sol REP-001 sidecar error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
