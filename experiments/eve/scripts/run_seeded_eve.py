#!/usr/bin/env python3
"""Run pinned EvE after deterministically seeding its three sampler RNG streams."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import hydra
from omegaconf import OmegaConf

from scaling_evolve.algorithms.eve import runner
from scaling_evolve.algorithms.eve.factory import EveFactory


STREAM_NAMES = ("solver_population", "optimizer_population", "worker_selection")
_ORIGINAL_FROM_CONFIG = EveFactory.from_config.__func__


def derive_stream_seed(experiment_seed: int, stream_name: str) -> int:
    """Domain-separate one public experiment seed into a stable 64-bit seed."""
    if stream_name not in STREAM_NAMES:
        raise ValueError("unknown EvE RNG stream")
    material = f"EconCSlib-EvE-Stage4-v1:{experiment_seed}:{stream_name}".encode()
    return int.from_bytes(hashlib.sha256(material).digest()[:8], "big")


def seed_factory(factory: Any, experiment_seed: int) -> dict[str, int]:
    """Seed every random.Random instance used by pinned EvE sampling."""
    if isinstance(experiment_seed, bool) or not 0 <= experiment_seed < 2**63:
        raise ValueError("experiment_seed must be an integer in [0, 2^63)")
    seeds = {
        name: derive_stream_seed(experiment_seed, name) for name in STREAM_NAMES
    }
    factory.loop.solver_pop._rng.seed(seeds["solver_population"])
    factory.loop.optimizer_pop._rng.seed(seeds["optimizer_population"])
    factory.loop.solver_workspace_builder._rng.seed(seeds["worker_selection"])
    return seeds


def _seeded_from_config(cls, config, solver_evaluator, **kwargs):
    factory = _ORIGINAL_FROM_CONFIG(cls, config, solver_evaluator, **kwargs)
    raw_seed = OmegaConf.select(config, "experiment_seed")
    if isinstance(raw_seed, bool) or not isinstance(raw_seed, int):
        factory.close()
        raise SystemExit("Stage 4 requires an integer experiment_seed")
    try:
        derived = seed_factory(factory, raw_seed)
    except ValueError as exc:
        factory.close()
        raise SystemExit(str(exc)) from exc

    run_root = Path(str(config.run_root))
    condition = OmegaConf.to_container(
        OmegaConf.select(config, "stage4_condition"), resolve=True
    )
    audit = {
        "schema_version": "1.0.0",
        "experiment_seed": raw_seed,
        "derived_stream_seeds": derived,
        "seeded_before_initial_guidance_and_loop": True,
        "controlled_scope": "EvE sampler and worker-selection random.Random streams",
        "uncontrolled_scope": "Codex/provider model sampling; pinned adapter exposes no model seed",
        "condition": condition,
    }
    audit_path = run_root / "eve-sampler-seed.json"
    audit_path.parent.mkdir(parents=True, exist_ok=True)
    audit_path.write_text(
        json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print("EvE sampler seed audit: " + json.dumps(audit, sort_keys=True))
    return factory


EveFactory.from_config = classmethod(_seeded_from_config)
runner.EveFactory = EveFactory


@hydra.main(version_base="1.3", config_path=None)
def main(config) -> None:
    """Load the caller-supplied absolute config directory, then run pinned EvE."""
    runner.run(config)


if __name__ == "__main__":
    main()
