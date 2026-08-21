#!/usr/bin/env python3
"""Safe entrypoint for the EconCSLib EvE Stage 0/Stage 1 sidecar."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SIDECAR_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = SIDECAR_ROOT.parents[1]
LOCK_PATH = SIDECAR_ROOT / "UPSTREAM.lock.json"
CONFIG_ROOT = SIDECAR_ROOT / "configs" / "eve"
OVERLAY_SOURCE = SIDECAR_ROOT / "overlay"
MANUAL_SOURCE = REPO_ROOT / "docs" / "research" / "mathlib-style" / "MANUAL_EN.md"
RUNTIME_ROOT = SIDECAR_ROOT / ".runtime"
RUNS_ROOT = RUNTIME_ROOT / "runs"
OFFICIAL_REMOTE = "github.com/scaling-group/eve"
DEFAULT_EXPERIMENT = "mathlib-style-smoke"
EXPECTED_LEAN_VERSION = "4.30.0"


class CheckError(RuntimeError):
    """Raised for a concise, non-secret sidecar preflight failure."""


@dataclass(frozen=True)
class CheckoutIdentity:
    root: Path
    remote: str
    commit: str


@dataclass(frozen=True)
class ExperimentSpec:
    """One fully allow-listed sidecar experiment and its evaluator fixtures."""

    cli_name: str
    config_name: str
    seed_root: Path
    evaluator: Path
    evaluation_step: Path
    fixtures: dict[str, Path]
    requires_model_quota_ack: bool
    overlay_key: str
    loop_config_name: str
    driver_config_name: str
    evaluator_args: tuple[str, ...] = ()
    stage4: bool = False


SMOKE_FIXTURE_ROOT = SIDECAR_ROOT / "smoke" / "expected"
EFG_FIXTURE_ROOT = SIDECAR_ROOT / "efg_reachability_micro" / "expected"
EXPERIMENTS = {
    DEFAULT_EXPERIMENT: ExperimentSpec(
        cli_name=DEFAULT_EXPERIMENT,
        config_name="mathlib_style_smoke",
        seed_root=SIDECAR_ROOT / "smoke" / "seed",
        evaluator=SIDECAR_ROOT / "scripts" / "evaluate_smoke.py",
        evaluation_step=SIDECAR_ROOT / "scripts" / "evaluation.sh",
        fixtures={
            "accepted": SMOKE_FIXTURE_ROOT / "Accepted.lean",
            "unfixed": SMOKE_FIXTURE_ROOT / "Unfixed.lean",
            "compile-failure": SMOKE_FIXTURE_ROOT / "CompileFailure.lean",
            "placeholder": SMOKE_FIXTURE_ROOT / "Placeholder.lean",
            "axiom": SMOKE_FIXTURE_ROOT / "Axiom.lean",
            "constant": SMOKE_FIXTURE_ROOT / "Constant.lean",
            "boundary": SMOKE_FIXTURE_ROOT / "Accepted.lean",
        },
        requires_model_quota_ack=False,
        overlay_key="",
        loop_config_name="smoke",
        driver_config_name="codex_offline",
    ),
    "efg-reachability-micro": ExperimentSpec(
        cli_name="efg-reachability-micro",
        config_name="efg_reachability_micro",
        seed_root=SIDECAR_ROOT / "efg_reachability_micro" / "seed",
        evaluator=SIDECAR_ROOT / "scripts" / "evaluate_efg_reachability_micro.py",
        evaluation_step=(
            SIDECAR_ROOT / "scripts" / "evaluation_efg_reachability_micro.sh"
        ),
        fixtures={
            "accepted": EFG_FIXTURE_ROOT / "Accepted.lean",
            "unfixed": (
                SIDECAR_ROOT / "efg_reachability_micro" / "seed" / "Candidate.lean"
            ),
            "compile-failure": EFG_FIXTURE_ROOT / "CompileFailure.lean",
            "placeholder": EFG_FIXTURE_ROOT / "Placeholder.lean",
            "axiom": EFG_FIXTURE_ROOT / "Axiom.lean",
            "constant": EFG_FIXTURE_ROOT / "Constant.lean",
            "boundary": EFG_FIXTURE_ROOT / "Accepted.lean",
            "forbidden-broad-import": EFG_FIXTURE_ROOT / "BroadImport.lean",
            "forbidden-additional-import": (
                EFG_FIXTURE_ROOT / "AdditionalImport.lean"
            ),
            "wrong-theorem-type": EFG_FIXTURE_ROOT / "WrongTheoremType.lean",
            "missing-diamond": EFG_FIXTURE_ROOT / "MissingDiamond.lean",
        },
        requires_model_quota_ack=True,
        overlay_key="efg_reachability_micro",
        loop_config_name="smoke",
        driver_config_name="codex_luna_offline",
    ),
    "entry-game-direct": ExperimentSpec(
        cli_name="entry-game-direct",
        config_name="entry_game_direct",
        seed_root=SIDECAR_ROOT / "stage2_entry_game" / "direct" / "seed",
        evaluator=SIDECAR_ROOT / "scripts" / "evaluate_stage2_entry_game.py",
        evaluation_step=SIDECAR_ROOT / "scripts" / "evaluation_stage2_entry_direct.sh",
        fixtures={
            "accepted": SIDECAR_ROOT / "stage2_entry_game" / "direct" / "expected" / "Accepted.lean",
            "unfixed": SIDECAR_ROOT / "stage2_entry_game" / "direct" / "seed" / "Candidate.lean",
        },
        requires_model_quota_ack=True,
        overlay_key="entry_game_direct",
        loop_config_name="stage4",
        driver_config_name="codex_luna_stage4",
        evaluator_args=("--route", "direct"),
        stage4=True,
    ),
    "entry-game-transport": ExperimentSpec(
        cli_name="entry-game-transport",
        config_name="entry_game_transport",
        seed_root=SIDECAR_ROOT / "stage2_entry_game" / "transport" / "seed",
        evaluator=SIDECAR_ROOT / "scripts" / "evaluate_stage2_entry_game.py",
        evaluation_step=SIDECAR_ROOT / "scripts" / "evaluation_stage2_entry_transport.sh",
        fixtures={
            "accepted": SIDECAR_ROOT / "stage2_entry_game" / "transport" / "expected" / "Accepted.lean",
            "unfixed": SIDECAR_ROOT / "stage2_entry_game" / "transport" / "seed" / "Candidate.lean",
        },
        requires_model_quota_ack=True,
        overlay_key="entry_game_transport",
        loop_config_name="stage4",
        driver_config_name="codex_luna_stage4",
        evaluator_args=("--route", "transport"),
        stage4=True,
    ),
}

STAGE4_CONDITIONS = ("static", "fixed", "evolved")
STAGE4_SEEDS = (1729, 2718)
STAGE4_GUIDANCE_HASHES = {
    ("entry-game-direct", "static"): "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    ("entry-game-direct", "fixed"): "47a43ca03b7266a112257d064af7d1968dbe7a09e9ec2ecae20b164285c0e743",
    ("entry-game-direct", "evolved"): "47a43ca03b7266a112257d064af7d1968dbe7a09e9ec2ecae20b164285c0e743",
    ("entry-game-transport", "static"): "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    ("entry-game-transport", "fixed"): "458d4ab45a20b57594a70f7ec62f72ba54ea1cdd635091091a70813e0edfaf24",
    ("entry-game-transport", "evolved"): "458d4ab45a20b57594a70f7ec62f72ba54ea1cdd635091091a70813e0edfaf24",
}


def _run(
    command: list[str],
    *,
    cwd: Path,
    env: dict[str, str] | None = None,
    timeout: int = 30,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=cwd,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
        timeout=timeout,
    )


def _run_with_isolated_uv_cache(
    command: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    timeout: int,
) -> subprocess.CompletedProcess[str]:
    """Run an offline uv probe without touching the user's global uv cache."""
    with tempfile.TemporaryDirectory(prefix="econ-cslib-eve-uv-cache-") as cache:
        isolated_env = {**env, "UV_CACHE_DIR": cache}
        return _run(command, cwd=cwd, env=isolated_env, timeout=timeout)


def _load_lock() -> dict[str, Any]:
    try:
        payload = json.loads(LOCK_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CheckError("UPSTREAM.lock.json is missing or invalid") from exc
    if not isinstance(payload, dict) or payload.get("status") != "scaffold-ready":
        raise CheckError("UPSTREAM.lock.json does not declare scaffold-ready")
    upstream = payload.get("upstream")
    if not isinstance(upstream, dict):
        raise CheckError("UPSTREAM.lock.json has no upstream identity")
    for key in ("repository", "tag", "tag_object_sha", "commit_sha"):
        value = upstream.get(key)
        if (
            not isinstance(value, str)
            or not re.fullmatch(r"[0-9a-f]{40}", value)
            and key.endswith("sha")
        ):
            raise CheckError(f"UPSTREAM.lock.json has an invalid {key}")
    return payload


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(65536):
            digest.update(chunk)
    return digest.hexdigest()


def _tree_sha256(root: Path) -> str:
    """Hash a guidance tree with stable relative-path and length framing."""
    digest = hashlib.sha256()
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        relative = path.relative_to(root).as_posix().encode("utf-8")
        content = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return digest.hexdigest()


def _validate_stage4_selection(
    spec: ExperimentSpec,
    *,
    condition: str | None,
    experiment_seed: int | None,
) -> None:
    if not spec.stage4:
        if condition is not None or experiment_seed is not None:
            raise CheckError("condition/experiment-seed are only valid for Stage 4 tasks")
        return
    if condition not in STAGE4_CONDITIONS:
        raise CheckError("Stage 4 requires --condition static, fixed, or evolved")
    if experiment_seed not in STAGE4_SEEDS:
        raise CheckError("Stage 4 experiment seed must be one of the frozen values 1729 or 2718")


def _normalize_remote(value: str) -> str:
    remote = value.strip().lower().removesuffix(".git").rstrip("/")
    remote = remote.removeprefix("https://").removeprefix("http://")
    remote = remote.removeprefix("ssh://git@")
    if remote.startswith("git@github.com:"):
        remote = "github.com/" + remote.removeprefix("git@github.com:")
    return remote


def _safe_checkout(path: Path) -> Path:
    resolved = path.expanduser().resolve()
    forbidden = {Path("/").resolve(), Path.home().resolve(), REPO_ROOT.resolve()}
    if resolved in forbidden:
        raise CheckError("EvE checkout path is too broad")
    try:
        resolved.relative_to(REPO_ROOT.resolve())
    except ValueError:
        pass
    else:
        raise CheckError("EvE checkout must be external to the EconCSLib repository")
    if not (resolved / ".git").exists():
        raise CheckError("EvE checkout is not a Git checkout")
    return resolved


def verify_checkout(path: Path) -> CheckoutIdentity:
    """Verify the official remote, peeled commit, tag object, and license files."""
    lock = _load_lock()
    upstream = lock["upstream"]
    license_lock = lock["license"]
    runtime_lock = lock["runtime_requirements"]
    checkout = _safe_checkout(path)

    remote_result = _run(["git", "remote", "get-url", "origin"], cwd=checkout)
    if remote_result.returncode != 0:
        raise CheckError("EvE checkout has no readable origin remote")
    remote = remote_result.stdout.strip()
    if _normalize_remote(remote) != OFFICIAL_REMOTE:
        raise CheckError(
            "EvE checkout origin is not the official scaling-group/eve repository"
        )

    commit_result = _run(["git", "rev-parse", "HEAD"], cwd=checkout)
    commit = commit_result.stdout.strip()
    if commit_result.returncode != 0 or commit != upstream["commit_sha"]:
        raise CheckError("EvE checkout commit does not match UPSTREAM.lock.json")

    tag_result = _run(
        ["git", "rev-parse", f"refs/tags/{upstream['tag']}"], cwd=checkout
    )
    if (
        tag_result.returncode != 0
        or tag_result.stdout.strip() != upstream["tag_object_sha"]
    ):
        raise CheckError("EvE annotated tag object does not match UPSTREAM.lock.json")
    peeled = _run(["git", "rev-parse", f"{upstream['tag']}^{{commit}}"], cwd=checkout)
    if peeled.returncode != 0 or peeled.stdout.strip() != commit:
        raise CheckError("EvE tag does not peel to the pinned commit")

    tracked = _run(
        ["git", "status", "--porcelain", "--untracked-files=no"], cwd=checkout
    )
    if tracked.returncode != 0 or tracked.stdout.strip():
        raise CheckError("EvE checkout has tracked modifications")

    for filename, key in (
        ("LICENSE", "license_file_sha256"),
        ("NOTICE", "notice_file_sha256"),
        ("pyproject.toml", "pyproject_sha256"),
        ("uv.lock", "uv_lock_sha256"),
    ):
        path_to_check = checkout / filename
        expected_hash = license_lock[key] if key in license_lock else runtime_lock[key]
        if not path_to_check.is_file() or _sha256(path_to_check) != expected_hash:
            raise CheckError(f"EvE {filename} does not match UPSTREAM.lock.json")
    if (checkout / ".python-version").read_text(encoding="utf-8").strip() != "3.13":
        raise CheckError("EvE .python-version does not match UPSTREAM.lock.json")
    return CheckoutIdentity(checkout, remote, commit)


def verify_stage4_upstream_semantics(identity: CheckoutIdentity) -> None:
    """Recheck every upstream source hash cited by the Stage 4 semantics audit."""
    path = SIDECAR_ROOT / "stage4_upstream_semantics.json"
    try:
        evidence = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CheckError("Stage 4 upstream semantics evidence is invalid") from exc
    if evidence.get("upstream", {}).get("commit") != identity.commit:
        raise CheckError("Stage 4 semantics evidence targets a different EvE commit")
    source_evidence = evidence.get("source_evidence")
    if not isinstance(source_evidence, list) or not source_evidence:
        raise CheckError("Stage 4 semantics evidence has no source records")
    for record in source_evidence:
        if not isinstance(record, dict):
            raise CheckError("Stage 4 semantics source record is invalid")
        relative = record.get("path")
        expected = record.get("sha256")
        if not isinstance(relative, str) or not isinstance(expected, str):
            raise CheckError("Stage 4 semantics source record is incomplete")
        source = (identity.root / relative).resolve()
        if not _is_relative_to(source, identity.root.resolve()):
            raise CheckError("Stage 4 semantics source path escaped upstream checkout")
        if not source.is_file() or _sha256(source) != expected:
            raise CheckError(f"Stage 4 upstream source hash mismatch: {relative}")


def verify_stage4_protocol_assets() -> None:
    """Fail closed when any artifact frozen by the Stage 4 protocol drifts."""
    path = SIDECAR_ROOT / "stage4_protocol.json"
    try:
        protocol = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CheckError("Stage 4 protocol is invalid") from exc
    if protocol.get("id") != "EVE-STAGE4-LUNA-ENTRY-GAME-DEV-002":
        raise CheckError("Stage 4 protocol identity mismatch")
    frozen = protocol.get("frozen_artifacts")
    if not isinstance(frozen, dict) or not frozen:
        raise CheckError("Stage 4 protocol has no frozen artifacts")
    for relative, expected in frozen.items():
        if not isinstance(relative, str) or not isinstance(expected, str):
            raise CheckError("Stage 4 frozen artifact record is invalid")
        artifact = (REPO_ROOT / relative).resolve()
        if not _is_relative_to(artifact, REPO_ROOT.resolve()):
            raise CheckError("Stage 4 frozen artifact escaped EconCSlib")
        if not artifact.is_file() or _sha256(artifact) != expected:
            raise CheckError(f"Stage 4 frozen artifact hash mismatch: {relative}")


def _required_sidecar_paths(spec: ExperimentSpec) -> tuple[Path, ...]:
    common = (
        CONFIG_ROOT / "runtime" / "sidecar.yaml",
        CONFIG_ROOT / "loop" / f"{spec.loop_config_name}.yaml",
        CONFIG_ROOT / "driver" / f"{spec.driver_config_name}.yaml",
        CONFIG_ROOT / "logger" / "local.yaml",
        SIDECAR_ROOT / "scripts" / "evaluator_common.py",
        CONFIG_ROOT / f"{spec.config_name}.yaml",
        CONFIG_ROOT / "application" / f"{spec.config_name}.yaml",
        CONFIG_ROOT / "evaluation" / f"{spec.config_name}.yaml",
        CONFIG_ROOT / "optimizer" / f"{spec.config_name}.yaml",
        spec.evaluator,
        spec.evaluation_step,
        spec.seed_root / "Candidate.lean",
        spec.seed_root / "README.md",
        spec.seed_root.parent / "case.json",
        *spec.fixtures.values(),
    )
    if spec.cli_name == DEFAULT_EXPERIMENT:
        return common + (
            OVERLAY_SOURCE / "initial_guidance" / "docs" / "mathlib_style.md",
            OVERLAY_SOURCE / "immutable" / "AGENTS.md",
            OVERLAY_SOURCE / "immutable" / "README.md",
            OVERLAY_SOURCE / "prompt" / "ENTRYPOINT.md",
            OVERLAY_SOURCE / "prompt" / "BOUNDARY_REPAIR.md",
            OVERLAY_SOURCE / "prompt" / "budget" / "USER.md",
            OVERLAY_SOURCE / "prompt" / "budget" / "TURN.md",
            MANUAL_SOURCE,
        )
    route_overlay = OVERLAY_SOURCE / spec.overlay_key
    overlay_paths = (
        route_overlay / "immutable" / "AGENTS.md",
        route_overlay / "immutable" / "README.md",
        route_overlay / "prompt" / "ENTRYPOINT.md",
        route_overlay / "prompt" / "BOUNDARY_REPAIR.md",
        route_overlay / "prompt" / "budget" / "USER.md",
        route_overlay / "prompt" / "budget" / "TURN.md",
    )
    if spec.cli_name == "efg-reachability-micro":
        return common + overlay_paths + (
            route_overlay / "initial_guidance" / "docs" / "structural_core.md",
            spec.seed_root.parent / "run-manifest.json",
        )
    guidance_name = "direct.md" if spec.cli_name.endswith("direct") else "transport.md"
    return common + overlay_paths + (
        route_overlay / "initial_guidance" / "docs" / guidance_name,
        CONFIG_ROOT / "condition" / "static.yaml",
        CONFIG_ROOT / "condition" / "fixed.yaml",
        CONFIG_ROOT / "condition" / "evolved.yaml",
        SIDECAR_ROOT / "scripts" / "run_seeded_eve.py",
        SIDECAR_ROOT / "stage4_protocol.json",
        SIDECAR_ROOT / "stage4_upstream_semantics.json",
    )


def verify_sidecar_assets(
    spec: ExperimentSpec = EXPERIMENTS[DEFAULT_EXPERIMENT],
) -> None:
    missing = [
        path.relative_to(REPO_ROOT).as_posix()
        for path in _required_sidecar_paths(spec)
        if not path.is_file()
    ]
    if missing:
        raise CheckError("Missing sidecar assets: " + ", ".join(missing))
    case = json.loads((spec.seed_root.parent / "case.json").read_text(encoding="utf-8"))
    if (
        case.get("editable_files") != ["Candidate.lean"]
        or case.get("editable_folders") != []
    ):
        raise CheckError("Experiment editable boundary is not the exact candidate file")
    score = case.get("score")
    if not isinstance(score, dict) or score.get("pass") != 1.0:
        raise CheckError("Experiment pass score is invalid")
    if score.get("failure") != 0.0 or score.get("boundary_failure") != 0.0:
        raise CheckError("Failure and boundary failure must use the same worst score")


def _dependency_probe(identity: CheckoutIdentity) -> bool:
    uv = shutil.which("uv")
    python = identity.root / ".venv" / "bin" / "python"
    if uv is None or not python.is_file():
        return False
    env = {
        **os.environ,
        "EVE_ECONCSLIB_ROOT": str(REPO_ROOT),
        "EVE_RUNTIME_OVERLAY_ROOT": str(OVERLAY_SOURCE),
        "EVE_SIDECAR_RUN_ROOT": str(RUNTIME_ROOT / "probe-run"),
        "EVE_STAGE4_GUIDANCE_ROOT": str(
            OVERLAY_SOURCE / "entry_game_direct" / "initial_guidance"
        ),
        "PYTHONPATH": str(identity.root / "src"),
    }
    config_cases: list[tuple[str, list[str]]] = []
    for spec in EXPERIMENTS.values():
        if spec.stage4:
            config_cases.extend(
                (
                    spec.config_name,
                    [f"condition={condition}", "experiment_seed=1729"],
                )
                for condition in STAGE4_CONDITIONS
            )
        else:
            config_cases.append((spec.config_name, []))
    script = f"""
from pathlib import Path
import importlib.util
import random
from types import SimpleNamespace
from hydra import compose, initialize_config_dir
from hydra.utils import instantiate
from scaling_evolve.algorithms.eve import runner as _runner
from scaling_evolve.algorithms.eve.factory import _load_solver_worker_configs
from scaling_evolve.algorithms.eve.workflow.evaluation import build_evaluation_plan

with initialize_config_dir(version_base="1.3", config_dir={str(CONFIG_ROOT)!r}):
    for config_name, overrides in {config_cases!r}:
        config = compose(config_name=config_name, overrides=overrides)
        assert list(config.application.editable.files) == ["Candidate.lean"]
        assert list(config.application.editable.folders) == []
        assert float(config.application.boundary_failure_score.score) == 0.0
        assert float(config.evaluation.failure_score.score) == 0.0
        assert Path(config.application.path).is_dir()
        assert Path(config.evaluation.steps[0]).is_file()
        assert Path(config.optimizer.initial_guidance).is_dir()
        assert len(_load_solver_worker_configs(config, search_root=Path({str(identity.root)!r}))) == 1
        assert len(build_evaluation_plan(
            None, evaluation_config=config.evaluation, search_root=Path({str(identity.root)!r})
        ).steps) == 1
        instantiate(config.optimizer.evaluation, _convert_="all")
        if config_name.startswith("entry_game_"):
            assert int(config.experiment_seed) == 1729
            condition = overrides[0].split("=", 1)[1]
            expected = 1 if condition == "evolved" else 0
            assert int(config.loop.produce_optimizer_in_phase2) == expected
            assert bool(config.loop.enable_resume) is False
        for key in (
            "working_optimizer", "solver_examples", "solver_prefill",
            "optimizer_examples", "produced_optimizers"
        ):
            instantiate(dict(config.loop.sampling[key]), _convert_="all")

wrapper_spec = importlib.util.spec_from_file_location(
    "econcslib_stage4_seed_wrapper",
    {str(SIDECAR_ROOT / "scripts" / "run_seeded_eve.py")!r},
)
assert wrapper_spec is not None and wrapper_spec.loader is not None
wrapper = importlib.util.module_from_spec(wrapper_spec)
wrapper_spec.loader.exec_module(wrapper)
fake = SimpleNamespace(
    loop=SimpleNamespace(
        solver_pop=SimpleNamespace(_rng=random.Random()),
        optimizer_pop=SimpleNamespace(_rng=random.Random()),
        solver_workspace_builder=SimpleNamespace(_rng=random.Random()),
    )
)
derived = wrapper.seed_factory(fake, 1729)
assert set(derived) == set(wrapper.STREAM_NAMES)
assert len(set(derived.values())) == 3
assert derived == wrapper.seed_factory(fake, 1729)
"""
    result = _run_with_isolated_uv_cache(
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


def _resolved_lean_toolchain_bin() -> Path:
    """Resolve the repository-selected direct Lean toolchain binaries."""
    elan = shutil.which("elan")
    if elan is None:
        raise CheckError("elan executable is unavailable")

    resolved: dict[str, Path] = {}
    for executable in ("lake", "lean"):
        result = _run(
            [elan, "which", executable],
            cwd=REPO_ROOT,
            timeout=20,
        )
        candidates = []
        for line in reversed(result.stdout.splitlines()):
            candidate = Path(line.strip()).expanduser()
            if candidate.is_file() and candidate.name == executable:
                candidates.append(candidate.resolve())
        if result.returncode != 0 or len(candidates) != 1:
            raise CheckError(
                f"Could not resolve the repository-selected direct {executable} binary"
            )
        resolved[executable] = candidates[0]

    toolchain_bin = resolved["lake"].parent
    if resolved["lean"].parent != toolchain_bin:
        raise CheckError("Resolved lake and lean binaries are from different toolchains")
    version = _run(
        [str(resolved["lean"]), "--version"],
        cwd=REPO_ROOT,
        timeout=20,
    )
    if version.returncode != 0 or f"version {EXPECTED_LEAN_VERSION}" not in version.stdout:
        raise CheckError(
            f"Resolved Lean toolchain is not the required {EXPECTED_LEAN_VERSION}"
        )
    return toolchain_bin


def _prepend_lean_toolchain_path(
    env: dict[str, str], toolchain_bin: Path
) -> dict[str, str]:
    updated = dict(env)
    current_path = updated.get("PATH", os.environ.get("PATH", ""))
    updated["PATH"] = os.pathsep.join(
        item for item in (str(toolchain_bin), current_path) if item
    )
    return updated


def _isolated_solver_lean_available(
    spec: ExperimentSpec,
    *,
    toolchain_bin: Path | None = None,
) -> bool:
    """Compile the accepted fixture with an isolated HOME and no elan fallback."""
    try:
        direct_bin = toolchain_bin or _resolved_lean_toolchain_bin()
    except CheckError:
        return False
    accepted = spec.fixtures.get("accepted")
    if accepted is None or not accepted.is_file():
        return False

    with tempfile.TemporaryDirectory(
        prefix="econ-cslib-eve-isolated-lean-home-"
    ) as raw_home:
        isolated_home = Path(raw_home)
        env = _prepend_lean_toolchain_path(os.environ.copy(), direct_bin)
        env.update(
            {
                "HOME": str(isolated_home),
                "CODEX_HOME": str(isolated_home / ".codex"),
                "CODEX_SANDBOX_NETWORK_DISABLED": "1",
            }
        )
        result = _run(
            ["lake", "env", "lean", str(accepted)],
            cwd=REPO_ROOT,
            env=env,
            timeout=90,
        )
        return result.returncode == 0 and not (isolated_home / ".elan").exists()


def _codex_auth_available(identity: CheckoutIdentity) -> bool:
    codex = shutil.which("codex")
    if codex is None:
        return False
    result = _run([codex, "login", "status"], cwd=identity.root, timeout=10)
    return result.returncode == 0


def _codex_hook_trust_available(identity: CheckoutIdentity) -> bool:
    uv = shutil.which("uv")
    if uv is None:
        return False
    script = """
from pathlib import Path

from scaling_evolve.providers.agent.codex_hooks import ensure_codex_hooks_trusted

ensure_codex_hooks_trusted(Path.cwd())
"""
    env = os.environ.copy()
    env["PYTHONPATH"] = str(identity.root / "src")
    result = _run_with_isolated_uv_cache(
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
        timeout=10,
    )
    return result.returncode == 0


def check(
    identity: CheckoutIdentity,
    spec: ExperimentSpec = EXPERIMENTS[DEFAULT_EXPERIMENT],
) -> int:
    verify_sidecar_assets(spec)
    try:
        lean_toolchain_bin = _resolved_lean_toolchain_bin()
    except CheckError:
        lean_toolchain_bin = None
    tools = {
        "git": shutil.which("git") is not None,
        "uv": shutil.which("uv") is not None,
        "python3": shutil.which("python3") is not None,
        "lake": shutil.which("lake") is not None,
        "isolated solver Lean toolchain": (
            lean_toolchain_bin is not None
            and _isolated_solver_lean_available(
                spec, toolchain_bin=lean_toolchain_bin
            )
        ),
        "codex executable": shutil.which("codex") is not None,
        "codex authentication": _codex_auth_available(identity),
        "codex hook trust": _codex_hook_trust_available(identity),
        "upstream locked environment": _dependency_probe(identity),
    }
    print(f"EvE upstream: available ({identity.commit})")
    for name, available in tools.items():
        print(f"{name}: {'available' if available else 'unavailable'}")
    print("Codex credential values: never inspected or printed")
    return 0 if all(tools.values()) else 1


def dry_run(
    identity: CheckoutIdentity,
    spec: ExperimentSpec = EXPERIMENTS[DEFAULT_EXPERIMENT],
    *,
    condition: str | None = None,
    experiment_seed: int | None = None,
) -> int:
    verify_sidecar_assets(spec)
    preview = {
        "action": "dry-run-only",
        "calls_codex": False,
        "network": False,
        "upstream_checkout": str(identity.root),
        "upstream_commit": identity.commit,
        "config_dir": str(CONFIG_ROOT),
        "experiment": spec.cli_name,
        "config_name": spec.config_name,
        "application_snapshot": str(spec.seed_root),
        "solver_editable_files": ["Candidate.lean"],
        "solver_editable_folders": [],
        "evaluation_step": str(spec.evaluation_step),
        "score_schema": {"score": "float", "summary": "string"},
        "score_direction": "higher-is-better",
        "pass_score": 1.0,
        "failure_score": 0.0,
        "boundary_failure_score": 0.0,
        "runtime_overlay": "materialized under the selected ignored run root",
        "run_root_parent": str(RUNS_ROOT),
        "model_quota_ack_required_for_execute": spec.requires_model_quota_ack,
        "stage4": spec.stage4,
        "condition": condition,
        "experiment_seed": experiment_seed,
        "eve_sampler_seed_controlled": spec.stage4,
        "provider_model_seed_controlled": False,
    }
    print(json.dumps(preview, indent=2, sort_keys=True))
    return 0


def evaluate_fixture(
    identity: CheckoutIdentity,
    fixture_name: str,
    spec: ExperimentSpec = EXPERIMENTS[DEFAULT_EXPERIMENT],
) -> int:
    _ = identity
    verify_sidecar_assets(spec)
    if fixture_name not in spec.fixtures:
        raise CheckError(
            f"Fixture '{fixture_name}' is not available for {spec.cli_name}"
        )
    fixture = spec.fixtures[fixture_name]
    with tempfile.TemporaryDirectory(prefix="econcslib-eve-fixture-") as raw_temp:
        candidate_dir = Path(raw_temp) / "candidate"
        shutil.copytree(spec.seed_root, candidate_dir)
        shutil.copy2(fixture, candidate_dir / "Candidate.lean")
        if fixture_name == "boundary":
            (candidate_dir / "Forbidden.txt").write_text(
                "boundary violation\n", encoding="utf-8"
            )
        score_path = Path(raw_temp) / "score.yaml"
        report_path = Path(raw_temp) / "evaluation.json"
        result = subprocess.run(
            [
                sys.executable,
                str(spec.evaluator),
                *spec.evaluator_args,
                "--candidate-dir",
                str(candidate_dir),
                "--score-output",
                str(score_path),
                "--report-output",
                str(report_path),
            ],
            cwd=REPO_ROOT,
            check=False,
        )
        if score_path.is_file():
            print(score_path.read_text(encoding="utf-8").strip())
        return result.returncode


def _new_run_root() -> Path:
    stamp = dt.datetime.now(dt.UTC).strftime("%Y%m%dT%H%M%S_%fZ")
    candidate = (RUNS_ROOT / stamp).resolve()
    if (
        not _is_relative_to(candidate, RUNS_ROOT.resolve())
        or candidate == RUNS_ROOT.resolve()
    ):
        raise CheckError("Generated run root escaped the sidecar runtime directory")
    if candidate.exists():
        raise CheckError("Generated run root already exists")
    return candidate


def _is_relative_to(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def _materialize_overlay(run_root: Path) -> Path:
    overlay = run_root / "overlay"
    shutil.copytree(OVERLAY_SOURCE, overlay)
    shutil.copy2(MANUAL_SOURCE, overlay / "immutable" / "MANUAL_EN.md")
    provenance = {
        "source": "docs/research/mathlib-style/MANUAL_EN.md",
        "sha256": _sha256(MANUAL_SOURCE),
        "copied_for": "immutable EvE worker context",
    }
    (overlay / "immutable" / "MANUAL_EN.source.json").write_text(
        json.dumps(provenance, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return overlay


def execute(
    identity: CheckoutIdentity,
    spec: ExperimentSpec = EXPERIMENTS[DEFAULT_EXPERIMENT],
    *,
    acknowledge_model_quota: bool = False,
    condition: str | None = None,
    experiment_seed: int | None = None,
) -> int:
    verify_sidecar_assets(spec)
    if spec.stage4:
        verify_stage4_protocol_assets()
        verify_stage4_upstream_semantics(identity)
    _validate_stage4_selection(
        spec, condition=condition, experiment_seed=experiment_seed
    )
    if spec.requires_model_quota_ack and not acknowledge_model_quota:
        raise CheckError(
            f"{spec.cli_name} execution requires --acknowledge-model-quota"
        )
    if not _dependency_probe(identity):
        raise CheckError(
            "Pinned EvE dependencies are unavailable; run 'uv sync --locked' in the external checkout"
        )
    if shutil.which("codex") is None:
        raise CheckError("Codex executable is unavailable")
    if not _codex_auth_available(identity):
        raise CheckError("Codex authentication is unavailable")
    lean_toolchain_bin = _resolved_lean_toolchain_bin()
    if not _isolated_solver_lean_available(
        spec, toolchain_bin=lean_toolchain_bin
    ):
        raise CheckError(
            "Pinned Lean toolchain is unavailable inside an isolated solver HOME"
        )

    run_root = _new_run_root()
    run_root.mkdir(parents=True)
    runtime_overlay = _materialize_overlay(run_root)
    stage4_guidance_root: Path | None = None
    if spec.stage4:
        assert condition is not None
        if condition == "static":
            stage4_guidance_root = run_root / "static-empty-guidance"
            stage4_guidance_root.mkdir()
        else:
            stage4_guidance_root = (
                runtime_overlay / spec.overlay_key / "initial_guidance"
            )
        actual_guidance_hash = _tree_sha256(stage4_guidance_root)
        expected_guidance_hash = STAGE4_GUIDANCE_HASHES[(spec.cli_name, condition)]
        if actual_guidance_hash != expected_guidance_hash:
            raise CheckError("Stage 4 initial guidance tree hash mismatch")
    env = _prepend_lean_toolchain_path({
        **os.environ,
        "EVE_ECONCSLIB_ROOT": str(REPO_ROOT),
        "EVE_RUNTIME_OVERLAY_ROOT": str(runtime_overlay),
        "EVE_SIDECAR_RUN_ROOT": str(run_root),
        "PYTHONPATH": str(identity.root / "src"),
        "UV_CACHE_DIR": str(run_root / "uv-cache"),
    }, lean_toolchain_bin)
    if stage4_guidance_root is not None:
        env["EVE_STAGE4_GUIDANCE_ROOT"] = str(stage4_guidance_root)
    command = [
        shutil.which("uv") or "uv",
        "run",
        "--offline",
        "--frozen",
        "--no-sync",
        "python",
        *(
            [str(SIDECAR_ROOT / "scripts" / "run_seeded_eve.py")]
            if spec.stage4
            else ["-m", "scaling_evolve.algorithms.eve.runner"]
        ),
        f"--config-dir={CONFIG_ROOT}",
        f"--config-name={spec.config_name}",
    ]
    if spec.stage4:
        assert condition is not None and experiment_seed is not None
        command.extend(
            [f"condition={condition}", f"experiment_seed={experiment_seed}"]
        )
        launch_record = {
            "schema_version": "1.0.0",
            "protocol_id": "EVE-STAGE4-LUNA-ENTRY-GAME-DEV-002",
            "protocol_sha256": _sha256(SIDECAR_ROOT / "stage4_protocol.json"),
            "experiment": spec.cli_name,
            "condition": condition,
            "experiment_seed": experiment_seed,
            "model": "gpt-5.6-luna",
            "reasoning_effort": "low",
            "iterations": 2,
            "attempt_limit": 1,
            "resume": False,
            "import": False,
            "initial_guidance_tree_sha256": _tree_sha256(stage4_guidance_root),
            "upstream_commit": identity.commit,
            "command": command,
            "status": "started",
            "exit_code": None,
        }
        launch_path = run_root / "stage4-launch.json"
        launch_path.write_text(
            json.dumps(launch_record, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    print(f"Starting explicit EvE execution; artifacts: {run_root}")
    completed = subprocess.run(command, cwd=identity.root, env=env, check=False)
    if spec.stage4:
        launch_record["status"] = (
            "completed" if completed.returncode == 0 else "failed"
        )
        launch_record["exit_code"] = completed.returncode
        launch_path.write_text(
            json.dumps(launch_record, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    return completed.returncode


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--eve-checkout",
        required=True,
        type=Path,
        help="Explicit path to the external official EvE v0.2.0 checkout",
    )
    parser.add_argument(
        "--experiment",
        choices=sorted(EXPERIMENTS),
        default=DEFAULT_EXPERIMENT,
        help=(
            "Hard-coded experiment selection; the existing smoke remains the default, "
            "and the EFG micro-pilot must be selected explicitly"
        ),
    )
    parser.add_argument(
        "--acknowledge-model-quota",
        action="store_true",
        help="Acknowledge that explicit EFG micro-pilot execution may consume model quota",
    )
    parser.add_argument(
        "--condition",
        choices=STAGE4_CONDITIONS,
        help="Frozen Stage 4 guidance condition (Stage 4 tasks only)",
    )
    parser.add_argument(
        "--experiment-seed",
        type=int,
        help="Frozen EvE sampler seed (1729 or 2718; Stage 4 tasks only)",
    )
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument("--check", action="store_true")
    actions.add_argument("--dry-run", action="store_true")
    actions.add_argument("--execute", action="store_true")
    fixture_names = sorted(
        {name for spec in EXPERIMENTS.values() for name in spec.fixtures}
    )
    actions.add_argument("--evaluate-fixture", choices=fixture_names)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        spec = EXPERIMENTS[args.experiment]
        if args.execute or args.dry_run:
            _validate_stage4_selection(
                spec,
                condition=args.condition,
                experiment_seed=args.experiment_seed,
            )
        elif args.condition is not None or args.experiment_seed is not None:
            raise CheckError("condition/experiment-seed are only used by dry-run or execute")
        identity = verify_checkout(args.eve_checkout)
        if spec.stage4:
            verify_stage4_protocol_assets()
            verify_stage4_upstream_semantics(identity)
        if args.check:
            return check(identity, spec)
        if args.dry_run:
            return dry_run(
                identity,
                spec,
                condition=args.condition,
                experiment_seed=args.experiment_seed,
            )
        if args.evaluate_fixture is not None:
            return evaluate_fixture(identity, args.evaluate_fixture, spec)
        if args.execute:
            return execute(
                identity,
                spec,
                acknowledge_model_quota=args.acknowledge_model_quota,
                condition=args.condition,
                experiment_seed=args.experiment_seed,
            )
        raise CheckError("No action selected")
    except (CheckError, OSError, subprocess.SubprocessError) as exc:
        print(f"EvE sidecar error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
