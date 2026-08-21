"""Structural tests for the EvE sidecar lock and four-layer overlay."""

from __future__ import annotations

import importlib.util
import io
import json
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock


SIDECAR_ROOT = Path(__file__).resolve().parents[1]


def _load_runner():
    path = SIDECAR_ROOT / "scripts" / "run.py"
    spec = importlib.util.spec_from_file_location("eve_sidecar_runner", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules["eve_sidecar_runner"] = module
    spec.loader.exec_module(module)
    return module


RUNNER = _load_runner()


class ScaffoldTests(unittest.TestCase):
    def test_operator_prompt_manifest_hashes_are_frozen(self) -> None:
        manifest = json.loads(
            (SIDECAR_ROOT / "operator_prompts" / "manifest.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertEqual(manifest["schema_version"], "1.0.0")
        self.assertEqual(len(manifest["prompts"]), 5)

        prompts = {prompt["id"]: prompt for prompt in manifest["prompts"]}
        preflight = prompts["EVE-STAGE1-LUNA-PREFLIGHT-001"]
        access_smoke = prompts["EVE-STAGE1-LUNA-ACCESS-SMOKE-001"]
        config_migration = prompts["EVE-STAGE1-LUNA-CONFIG-MIGRATION-001"]
        efg_manual_smoke = prompts["EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-001"]
        efg_manual_smoke_002 = prompts[
            "EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-002"
        ]

        for prompt in prompts.values():
            prompt_path = SIDECAR_ROOT.parents[1] / prompt["path"]
            self.assertEqual(prompt["version"], "1.0.0")
            self.assertEqual(prompt["model_target"], "gpt-5.6-luna")
            self.assertEqual(prompt["sha256"], RUNNER._sha256(prompt_path))

        self.assertEqual(preflight["status"], "EXECUTED_READY")
        self.assertEqual(
            preflight["execution_status"],
            "READY_FOR_SEPARATE_MODEL_ACCESS_SMOKE",
        )
        self.assertFalse(preflight["model_call_authorized"])
        self.assertEqual(access_smoke["status"], "EXECUTED_PASSED")
        self.assertEqual(
            access_smoke["execution_status"], "LUNA_ACCESS_SMOKE_PASSED"
        )
        self.assertEqual(access_smoke["model_call_attempts"], 1)
        self.assertTrue(access_smoke["model_call_authorized"])
        self.assertEqual(config_migration["status"], "EXECUTED_READY")
        self.assertEqual(
            config_migration["execution_status"], "LUNA_CONFIG_MIGRATION_READY"
        )
        self.assertEqual(config_migration["model_call_attempts"], 0)
        self.assertFalse(config_migration["model_call_authorized"])
        self.assertEqual(efg_manual_smoke["status"], "EXECUTED_COMPLETED")
        self.assertEqual(
            efg_manual_smoke["execution_status"],
            "LUNA_EFG_MANUAL_SMOKE_COMPLETED",
        )
        self.assertTrue(efg_manual_smoke["model_call_authorized"])
        self.assertTrue(efg_manual_smoke["eve_execute_authorized"])
        self.assertEqual(efg_manual_smoke["authorized_eve_execute_attempts"], 1)
        self.assertEqual(efg_manual_smoke["authorized_codex_sessions"], 1)
        self.assertEqual(efg_manual_smoke["agent_turn_limit"], 10)
        self.assertEqual(
            efg_manual_smoke["authorized_conditions"], ["EvE-evolved-guidance"]
        )
        self.assertEqual(efg_manual_smoke["eve_execute_attempts"], 1)
        self.assertEqual(efg_manual_smoke["codex_session_attempts"], 1)
        self.assertEqual(efg_manual_smoke["observed_agent_turns"], 5)
        self.assertEqual(efg_manual_smoke["candidate_score"], 0.0)
        self.assertFalse(efg_manual_smoke["guidance_modified"])

        self.assertEqual(efg_manual_smoke_002["status"], "EXECUTED_COMPLETED")
        self.assertEqual(
            efg_manual_smoke_002["execution_status"],
            "LUNA_EFG_MANUAL_SMOKE_002_COMPLETED",
        )
        self.assertTrue(efg_manual_smoke_002["model_call_authorized"])
        self.assertTrue(efg_manual_smoke_002["eve_execute_authorized"])
        self.assertEqual(
            efg_manual_smoke_002["authorized_eve_execute_attempts"], 1
        )
        self.assertEqual(efg_manual_smoke_002["authorized_codex_sessions"], 1)
        self.assertFalse(efg_manual_smoke_002["prior_prompt_budget_reused"])
        self.assertEqual(efg_manual_smoke_002["eve_execute_attempts"], 1)
        self.assertEqual(efg_manual_smoke_002["codex_session_attempts"], 1)
        self.assertEqual(efg_manual_smoke_002["observed_agent_turns"], 5)
        self.assertEqual(efg_manual_smoke_002["candidate_score"], 1.0)
        self.assertFalse(efg_manual_smoke_002["guidance_modified"])
        for key in ("execution_report", "post_run_audit"):
            artifact_path = SIDECAR_ROOT.parents[1] / efg_manual_smoke_002[key]
            self.assertTrue(artifact_path.is_file())
            self.assertEqual(
                efg_manual_smoke_002[f"{key}_sha256"],
                RUNNER._sha256(artifact_path),
            )
        self.assertEqual(
            efg_manual_smoke_002["authorized_conditions"],
            ["EvE-evolved-guidance"],
        )

        for historical_prompt in (preflight, access_smoke, config_migration):
            self.assertFalse(historical_prompt["eve_execute_authorized"])

    def test_luna_efg_manual_smoke_is_single_condition_and_no_retry(self) -> None:
        smoke_text = (
            SIDECAR_ROOT
            / "operator_prompts"
            / "STAGE1_LUNA_EFG_MANUAL_SMOKE.md"
        ).read_text(encoding="utf-8")
        self.assertIn("EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-001", smoke_text)
        self.assertIn("`EvE-evolved-guidance` condition", smoke_text)
        self.assertIn("`gpt-5.6-luna`", smoke_text)
        self.assertIn("exactly one Codex solver session", smoke_text)
        self.assertIn("at most 10 agent turns", smoke_text)
        self.assertIn("Boundary-repair attempts: 0", smoke_text)
        self.assertIn("--experiment efg-reachability-micro", smoke_text)
        self.assertIn("--acknowledge-model-quota", smoke_text)
        self.assertIn("--execute", smoke_text)
        self.assertIn("Do not invoke `codex exec` directly", smoke_text)
        self.assertIn("Do not rerun", smoke_text)
        self.assertIn("score 0 alone", smoke_text)
        self.assertIn("static/no-specialized-guidance", smoke_text)
        self.assertIn("fixed-initial-guidance", smoke_text)
        self.assertIn("no resume", smoke_text)

    def test_luna_efg_manual_smoke_002_requires_repaired_isolated_lean(self) -> None:
        smoke_text = (
            SIDECAR_ROOT
            / "operator_prompts"
            / "STAGE1_LUNA_EFG_MANUAL_SMOKE_002.md"
        ).read_text(encoding="utf-8")
        self.assertIn("EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-002", smoke_text)
        self.assertIn("Prompt 001 is permanently consumed", smoke_text)
        self.assertIn("not a retry under its budget", smoke_text)
        self.assertIn("isolated solver Lean toolchain: available", smoke_text)
        self.assertIn("exactly 45 passes", smoke_text)
        self.assertIn("Required Lean version: 4.30.0", smoke_text)
        self.assertIn("Do not set `HOME` or `ELAN_HOME`", smoke_text)
        self.assertIn("--experiment efg-reachability-micro", smoke_text)
        self.assertIn("--acknowledge-model-quota", smoke_text)
        self.assertIn("--execute", smoke_text)
        self.assertIn("Do not rerun", smoke_text)
        self.assertIn("score: 0.0", smoke_text)
        self.assertIn("static/fixed conditions", smoke_text)
        self.assertIn("no resume", smoke_text)

    def test_luna_config_migration_prompt_has_no_execution_authority(self) -> None:
        migration_text = (
            SIDECAR_ROOT
            / "operator_prompts"
            / "STAGE1_LUNA_CONFIG_MIGRATION.md"
        ).read_text(encoding="utf-8")
        self.assertIn("EVE-STAGE1-LUNA-CONFIG-MIGRATION-001", migration_text)
        self.assertIn("model: gpt-5.6-luna", migration_text)
        self.assertIn("driver: codex_luna_offline", migration_text)
        self.assertIn("model_calls\": 0", migration_text)
        self.assertIn("Do not edit", migration_text)
        self.assertIn("legacy Stage 0 driver remains `gpt-5.4-mini`", migration_text)
        self.assertIn("model_verbosity=\"codex-default-unpinned\"", migration_text)
        self.assertIn("no model call", migration_text)
        self.assertIn("`codex exec`", migration_text)
        self.assertIn("no `--execute`", migration_text)

    def test_luna_access_smoke_has_single_turn_safety_contract(self) -> None:
        access_text = (
            SIDECAR_ROOT / "operator_prompts" / "STAGE1_LUNA_ACCESS_SMOKE.md"
        ).read_text(encoding="utf-8")
        self.assertIn("Model-turn budget: exactly `1`", access_text)
        self.assertIn("--model gpt-5.6-luna", access_text)
        self.assertIn("--sandbox read-only", access_text)
        self.assertIn("--ephemeral", access_text)
        self.assertIn("--json", access_text)
        self.assertIn("Do not rerun the command", access_text)
        self.assertEqual(access_text.count("--dangerously-bypass-hook-trust"), 1)

    def test_lock_has_immutable_official_identity(self) -> None:
        lock = json.loads(
            (SIDECAR_ROOT / "UPSTREAM.lock.json").read_text(encoding="utf-8")
        )
        self.assertEqual(lock["status"], "scaffold-ready")
        self.assertEqual(
            lock["upstream"]["repository"], "https://github.com/scaling-group/eve"
        )
        self.assertEqual(lock["upstream"]["tag"], "v0.2.0")
        self.assertRegex(lock["upstream"]["commit_sha"], r"^[0-9a-f]{40}$")
        self.assertFalse(lock["integration"]["vendored"])
        self.assertFalse(lock["integration"]["submodule"])

    def test_remote_normalization_accepts_official_https_and_ssh(self) -> None:
        expected = "github.com/scaling-group/eve"
        self.assertEqual(
            RUNNER._normalize_remote("https://github.com/scaling-group/eve.git"),
            expected,
        )
        self.assertEqual(
            RUNNER._normalize_remote("git@github.com:scaling-group/eve.git"), expected
        )

    def test_all_four_layer_configs_and_exact_boundaries_exist(self) -> None:
        config_root = SIDECAR_ROOT / "configs" / "eve"
        for config_name in (
            "mathlib_style_smoke",
            "efg_reachability_micro",
            "entry_game_direct",
            "entry_game_transport",
        ):
            for relative in (
                f"{config_name}.yaml",
                f"application/{config_name}.yaml",
                f"evaluation/{config_name}.yaml",
                f"optimizer/{config_name}.yaml",
            ):
                self.assertTrue((config_root / relative).is_file(), relative)
            application = (
                config_root / "application" / f"{config_name}.yaml"
            ).read_text(encoding="utf-8")
            self.assertIn("Candidate.lean", application)
            self.assertIn("    folders: []", application)
            self.assertIn("    score: 0.0", application)

    def test_execute_is_the_only_runner_path_that_launches_upstream(self) -> None:
        source = (SIDECAR_ROOT / "scripts" / "run.py").read_text(encoding="utf-8")
        self.assertIn("def execute(\n", source)
        dry_run_body = source[
            source.index("def dry_run(") : source.index("def evaluate_fixture(")
        ]
        self.assertNotIn("subprocess.run", dry_run_body)
        self.assertNotIn("scaling_evolve.algorithms.eve.runner", dry_run_body)
        execute_body = source[source.index("def execute(\n") : source.index("def _parser(")]
        self.assertIn('"UV_CACHE_DIR": str(run_root / "uv-cache")', execute_body)
        self.assertIn("_resolved_lean_toolchain_bin()", execute_body)
        self.assertIn("_isolated_solver_lean_available(", execute_body)
        self.assertIn("_prepend_lean_toolchain_path({", execute_body)

    def test_execute_prepends_direct_lean_toolchain_to_solver_path(self) -> None:
        spec = RUNNER.EXPERIMENTS["efg-reachability-micro"]
        identity = RUNNER.CheckoutIdentity(Path("/tmp/eve"), "official", "0" * 40)
        completed = RUNNER.subprocess.CompletedProcess([], 0, "", "")
        with tempfile.TemporaryDirectory(prefix="eve-execute-env-") as raw_temp:
            temp_root = Path(raw_temp)
            run_root = temp_root / "run"
            toolchain_bin = temp_root / "toolchain" / "bin"
            with mock.patch.object(RUNNER, "verify_sidecar_assets"):
                with mock.patch.object(RUNNER, "_dependency_probe", return_value=True):
                    with mock.patch.object(RUNNER.shutil, "which", return_value="/usr/bin/codex"):
                        with mock.patch.object(RUNNER, "_codex_auth_available", return_value=True):
                            with mock.patch.object(
                                RUNNER,
                                "_resolved_lean_toolchain_bin",
                                return_value=toolchain_bin,
                            ):
                                with mock.patch.object(
                                    RUNNER,
                                    "_isolated_solver_lean_available",
                                    return_value=True,
                                ):
                                    with mock.patch.object(
                                        RUNNER, "_new_run_root", return_value=run_root
                                    ):
                                        with mock.patch.object(
                                            RUNNER,
                                            "_materialize_overlay",
                                            return_value=temp_root / "overlay",
                                        ):
                                            with mock.patch.object(
                                                RUNNER.subprocess,
                                                "run",
                                                return_value=completed,
                                            ) as run:
                                                self.assertEqual(
                                                    RUNNER.execute(
                                                        identity,
                                                        spec,
                                                        acknowledge_model_quota=True,
                                                    ),
                                                    0,
                                                )

            execution_env = run.call_args.kwargs["env"]
            self.assertEqual(
                execution_env["PATH"].split(os.pathsep)[0], str(toolchain_bin)
            )
            self.assertEqual(execution_env["UV_CACHE_DIR"], str(run_root / "uv-cache"))
            self.assertNotIn("ELAN_HOME", execution_env)

    def test_launcher_has_only_four_hard_coded_experiments(self) -> None:
        self.assertEqual(
            set(RUNNER.EXPERIMENTS),
            {
                "mathlib-style-smoke",
                "efg-reachability-micro",
                "entry-game-direct",
                "entry-game-transport",
            },
        )
        parser = RUNNER._parser()
        args = parser.parse_args(
            ["--eve-checkout", "/tmp/eve", "--dry-run"]
        )
        self.assertEqual(args.experiment, "mathlib-style-smoke")
        with redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit):
                parser.parse_args(
                    [
                        "--eve-checkout",
                        "/tmp/eve",
                        "--experiment",
                        "../../arbitrary",
                        "--dry-run",
                    ]
                )

    def test_efg_execution_requires_explicit_quota_acknowledgement(self) -> None:
        spec = RUNNER.EXPERIMENTS["efg-reachability-micro"]
        identity = RUNNER.CheckoutIdentity(Path("/tmp/eve"), "official", "0" * 40)
        with self.assertRaisesRegex(
            RUNNER.CheckError, "--acknowledge-model-quota"
        ):
            RUNNER.execute(identity, spec, acknowledge_model_quota=False)

    def test_stage4_selection_is_frozen_and_complete(self) -> None:
        spec = RUNNER.EXPERIMENTS["entry-game-direct"]
        RUNNER._validate_stage4_selection(
            spec, condition="static", experiment_seed=1729
        )
        RUNNER._validate_stage4_selection(
            spec, condition="evolved", experiment_seed=2718
        )
        with self.assertRaises(RUNNER.CheckError):
            RUNNER._validate_stage4_selection(
                spec, condition=None, experiment_seed=1729
            )
        with self.assertRaises(RUNNER.CheckError):
            RUNNER._validate_stage4_selection(
                spec, condition="fixed", experiment_seed=999
            )
        with self.assertRaises(RUNNER.CheckError):
            RUNNER._validate_stage4_selection(
                RUNNER.EXPERIMENTS["efg-reachability-micro"],
                condition="fixed",
                experiment_seed=1729,
            )

    def test_stage4_protocol_has_complete_paired_matrix(self) -> None:
        RUNNER.verify_stage4_protocol_assets()
        protocol = json.loads(
            (SIDECAR_ROOT / "stage4_protocol.json").read_text(encoding="utf-8")
        )
        matrix = protocol["run_matrix"]
        self.assertEqual(len(matrix), 12)
        self.assertEqual(protocol["maximum_model_sessions"], 24)
        self.assertEqual(
            {
                (item["task"], item["condition"], item["seed"])
                for item in matrix
            },
            {
                (task, condition, seed)
                for task in ("entry-game-direct", "entry-game-transport")
                for seed in RUNNER.STAGE4_SEEDS
                for condition in RUNNER.STAGE4_CONDITIONS
            },
        )
        self.assertFalse(protocol["pairing"]["provider_model_seed_controlled"])
        self.assertEqual(protocol["shared_compute"]["attempts_per_matrix_cell"], 1)

    def test_stage4_guidance_tree_hashes_are_frozen(self) -> None:
        with tempfile.TemporaryDirectory(prefix="eve-empty-") as raw_empty:
            empty_hash = RUNNER._tree_sha256(Path(raw_empty))
        self.assertEqual(
            empty_hash,
            RUNNER.STAGE4_GUIDANCE_HASHES[("entry-game-direct", "static")],
        )
        for experiment in ("entry-game-direct", "entry-game-transport"):
            spec = RUNNER.EXPERIMENTS[experiment]
            actual = RUNNER._tree_sha256(
                RUNNER.OVERLAY_SOURCE / spec.overlay_key / "initial_guidance"
            )
            self.assertEqual(
                actual, RUNNER.STAGE4_GUIDANCE_HASHES[(experiment, "fixed")]
            )
            self.assertEqual(
                actual, RUNNER.STAGE4_GUIDANCE_HASHES[(experiment, "evolved")]
            )

    def test_stage4_execute_uses_seed_wrapper_and_writes_launch_record(self) -> None:
        spec = RUNNER.EXPERIMENTS["entry-game-direct"]
        identity = RUNNER.CheckoutIdentity(Path("/tmp/eve"), "official", "0" * 40)
        completed = RUNNER.subprocess.CompletedProcess([], 0, "", "")
        with tempfile.TemporaryDirectory(prefix="eve-stage4-execute-") as raw_temp:
            root = Path(raw_temp)
            run_root = root / "run"
            toolchain_bin = root / "toolchain" / "bin"
            with mock.patch.object(RUNNER, "verify_sidecar_assets"), mock.patch.object(
                RUNNER, "verify_stage4_upstream_semantics"
            ), mock.patch.object(
                RUNNER, "_dependency_probe", return_value=True
            ), mock.patch.object(
                RUNNER.shutil, "which", return_value="/usr/bin/codex"
            ), mock.patch.object(
                RUNNER, "_codex_auth_available", return_value=True
            ), mock.patch.object(
                RUNNER, "_resolved_lean_toolchain_bin", return_value=toolchain_bin
            ), mock.patch.object(
                RUNNER, "_isolated_solver_lean_available", return_value=True
            ), mock.patch.object(
                RUNNER, "_new_run_root", return_value=run_root
            ), mock.patch.object(
                RUNNER, "_materialize_overlay", return_value=root / "overlay"
            ), mock.patch.object(
                RUNNER.subprocess, "run", return_value=completed
            ) as run:
                result = RUNNER.execute(
                    identity,
                    spec,
                    acknowledge_model_quota=True,
                    condition="static",
                    experiment_seed=1729,
                )

            self.assertEqual(result, 0)
            command = run.call_args.args[0]
            self.assertIn(str(SIDECAR_ROOT / "scripts" / "run_seeded_eve.py"), command)
            self.assertIn("condition=static", command)
            self.assertIn("experiment_seed=1729", command)
            launch = json.loads(
                (run_root / "stage4-launch.json").read_text(encoding="utf-8")
            )
            self.assertEqual(launch["status"], "completed")
            self.assertEqual(launch["exit_code"], 0)
            self.assertEqual(launch["attempt_limit"], 1)
            self.assertEqual(
                launch["initial_guidance_tree_sha256"],
                RUNNER.STAGE4_GUIDANCE_HASHES[("entry-game-direct", "static")],
            )
            self.assertEqual(
                run.call_args.kwargs["env"]["EVE_STAGE4_GUIDANCE_ROOT"],
                str(run_root / "static-empty-guidance"),
            )

    def test_dry_run_calls_no_subprocess_runner_codex_or_network(self) -> None:
        spec = RUNNER.EXPERIMENTS["efg-reachability-micro"]
        identity = RUNNER.CheckoutIdentity(Path("/tmp/eve"), "official", "0" * 40)
        output = io.StringIO()
        with mock.patch.object(
            RUNNER.subprocess,
            "run",
            side_effect=AssertionError("dry-run attempted a subprocess"),
        ):
            with redirect_stdout(output):
                self.assertEqual(RUNNER.dry_run(identity, spec), 0)
        preview = json.loads(output.getvalue())
        self.assertFalse(preview["calls_codex"])
        self.assertFalse(preview["network"])
        self.assertEqual(preview["experiment"], "efg-reachability-micro")

    def test_fixture_path_does_not_invoke_codex_or_upstream_runner(self) -> None:
        source = (SIDECAR_ROOT / "scripts" / "run.py").read_text(encoding="utf-8")
        body = source[
            source.index("def evaluate_fixture(") : source.index("def _new_run_root(")
        ]
        self.assertNotIn("codex", body.lower())
        self.assertNotIn("scaling_evolve", body)

    def test_dependency_probe_composes_all_configs_and_conditions(self) -> None:
        source = (SIDECAR_ROOT / "scripts" / "run.py").read_text(encoding="utf-8")
        body = source[
            source.index("def _dependency_probe(") : source.index(
                "def _codex_auth_available("
            )
        ]
        self.assertIn("for spec in EXPERIMENTS.values()", body)
        self.assertIn("for config_name", body)
        self.assertIn("compose(config_name=config_name, overrides=overrides)", body)
        self.assertIn('"--offline"', body)
        self.assertIn('"--frozen"', body)
        self.assertIn('"--no-sync"', body)
        self.assertNotIn("[str(python),", body)
        self.assertIn('"PYTHONPATH": str(identity.root / "src")', body)
        self.assertIn("_run_with_isolated_uv_cache(", body)
        self.assertEqual(
            source.count('"PYTHONPATH": str(identity.root / "src")'), 2
        )

    def test_uv_probe_cache_is_isolated_writable_and_ephemeral(self) -> None:
        completed = RUNNER.subprocess.CompletedProcess([], 0, "", "")
        observed_cache: Path | None = None

        def observe_run(*args, **kwargs):
            nonlocal observed_cache
            observed_cache = Path(kwargs["env"]["UV_CACHE_DIR"])
            self.assertTrue(observed_cache.is_dir())
            self.assertTrue(os.access(observed_cache, os.W_OK))
            return completed

        with mock.patch.object(RUNNER, "_run", side_effect=observe_run):
            result = RUNNER._run_with_isolated_uv_cache(
                ["uv", "run"],
                cwd=Path("/tmp"),
                env={"PYTHONPATH": "/tmp/eve/src"},
                timeout=10,
            )

        self.assertEqual(result.returncode, 0)
        self.assertIsNotNone(observed_cache)
        self.assertFalse(observed_cache.exists())

    def test_codex_hook_trust_probe_is_offline_and_credential_free(self) -> None:
        identity = RUNNER.CheckoutIdentity(Path("/tmp/eve"), "official", "0" * 40)
        completed = RUNNER.subprocess.CompletedProcess([], 0, "", "")
        with mock.patch.object(RUNNER.shutil, "which", return_value="/usr/bin/uv"):
            with mock.patch.object(RUNNER, "_run", return_value=completed) as run:
                self.assertTrue(RUNNER._codex_hook_trust_available(identity))

        command = run.call_args.args[0]
        self.assertEqual(command[:5], [
            "/usr/bin/uv",
            "run",
            "--offline",
            "--frozen",
            "--no-sync",
        ])
        self.assertIn("ensure_codex_hooks_trusted", command[-1])
        self.assertNotIn("login", command)
        self.assertEqual(
            run.call_args.kwargs["env"]["PYTHONPATH"], "/tmp/eve/src"
        )
        cache = Path(run.call_args.kwargs["env"]["UV_CACHE_DIR"])
        self.assertTrue(cache.name.startswith("econ-cslib-eve-uv-cache-"))
        self.assertFalse(cache.exists())

    def test_actual_hydra_loader_parses_both_configs_when_checkout_is_supplied(
        self,
    ) -> None:
        raw_checkout = os.environ.get("EVE_V020_TEST_CHECKOUT")
        if raw_checkout is None:
            self.skipTest("no explicit locked EvE v0.2.0 checkout supplied")
        identity = RUNNER.verify_checkout(Path(raw_checkout))
        self.assertTrue(RUNNER._dependency_probe(identity))

        uv = RUNNER.shutil.which("uv")
        self.assertIsNotNone(uv)
        env = {
            **os.environ,
            "EVE_ECONCSLIB_ROOT": str(RUNNER.REPO_ROOT),
            "EVE_RUNTIME_OVERLAY_ROOT": str(RUNNER.OVERLAY_SOURCE),
            "EVE_SIDECAR_RUN_ROOT": str(RUNNER.RUNTIME_ROOT / "test-compose-run"),
            "EVE_STAGE4_GUIDANCE_ROOT": str(
                RUNNER.OVERLAY_SOURCE / "entry_game_direct" / "initial_guidance"
            ),
            "PYTHONPATH": str(identity.root / "src"),
        }
        script = f"""
from hydra import compose, initialize_config_dir

with initialize_config_dir(version_base="1.3", config_dir={str(RUNNER.CONFIG_ROOT)!r}):
    stage0 = compose(config_name="mathlib_style_smoke")
    efg = compose(config_name="efg_reachability_micro")
    direct_static = compose(
        config_name="entry_game_direct",
        overrides=["condition=static", "experiment_seed=1729"],
    )
    direct_fixed = compose(
        config_name="entry_game_direct",
        overrides=["condition=fixed", "experiment_seed=1729"],
    )
    direct_evolved = compose(
        config_name="entry_game_direct",
        overrides=["condition=evolved", "experiment_seed=1729"],
    )
    transport_evolved = compose(
        config_name="entry_game_transport",
        overrides=["condition=evolved", "experiment_seed=2718"],
    )

assert stage0.driver.model == "gpt-5.4-mini"
assert stage0.driver.reasoning_effort == "low"
assert int(stage0.driver.rollout_max_turns) == 10
assert stage0.driver.web_search == "disabled"
assert int(stage0.driver.timeout_seconds) == 900
assert stage0.driver.overrides.solver.reasoning_effort == "low"

assert efg.driver.model == "gpt-5.6-luna"
assert efg.driver.reasoning_effort == "low"
assert int(efg.driver.rollout_max_turns) == 10
assert efg.driver.web_search == "disabled"
assert int(efg.driver.timeout_seconds) == 900
assert efg.driver.overrides.solver.reasoning_effort == "low"

assert direct_static.driver.model == "gpt-5.6-luna"
assert int(direct_static.driver.rollout_max_turns) == 6
assert int(direct_static.loop.max_iterations) == 2
assert int(direct_static.loop.produce_optimizer_in_phase2) == 0
assert direct_static.stage4_condition.initial_guidance_mode == "empty-runtime-directory"
assert int(direct_fixed.loop.produce_optimizer_in_phase2) == 0
assert direct_fixed.stage4_condition.initial_guidance_mode == "frozen-route-guidance"
assert int(direct_evolved.loop.produce_optimizer_in_phase2) == 1
assert direct_evolved.stage4_condition.optimizer_evolution
assert int(transport_evolved.experiment_seed) == 2718
assert int(transport_evolved.loop.produce_optimizer_in_phase2) == 1
assert not bool(transport_evolved.loop.enable_resume)
"""
        result = RUNNER._run_with_isolated_uv_cache(
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
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_accepted_efg_fixture_compiles_in_isolated_solver_home(self) -> None:
        raw_checkout = os.environ.get("EVE_V020_TEST_CHECKOUT")
        if raw_checkout is None:
            self.skipTest("no explicit locked EvE v0.2.0 checkout supplied")
        RUNNER.verify_checkout(Path(raw_checkout))
        spec = RUNNER.EXPERIMENTS["efg-reachability-micro"]
        toolchain_bin = RUNNER._resolved_lean_toolchain_bin()
        self.assertTrue(
            RUNNER._isolated_solver_lean_available(
                spec, toolchain_bin=toolchain_bin
            )
        )

    def test_luna_manual_smoke_history_is_hash_anchored_and_bounded(self) -> None:
        config_root = SIDECAR_ROOT / "configs" / "eve"
        legacy_driver = (config_root / "driver" / "codex_offline.yaml").read_text(
            encoding="utf-8"
        )
        luna_driver_path = config_root / "driver" / "codex_luna_offline.yaml"
        luna_driver = luna_driver_path.read_text(encoding="utf-8")
        efg_config_path = config_root / "efg_reachability_micro.yaml"
        efg_config = efg_config_path.read_text(encoding="utf-8")
        stage0_config = (config_root / "mathlib_style_smoke.yaml").read_text(
            encoding="utf-8"
        )

        self.assertIn("  model: gpt-5.4-mini\n", legacy_driver)
        self.assertNotIn("gpt-5.6", legacy_driver)
        self.assertIn("  - driver: codex_offline\n", stage0_config)
        self.assertIn("  - driver: codex_luna_offline\n", efg_config)
        self.assertNotIn("  - driver: codex_offline\n", efg_config)
        self.assertEqual(luna_driver.count("  model: gpt-5.6-luna\n"), 1)
        self.assertNotIn("  model: gpt-5.4-mini\n", luna_driver)
        self.assertNotIn("  model: gpt-5.6\n", luna_driver)
        self.assertIn("  reasoning_effort: low\n", luna_driver)
        self.assertIn("  rollout_max_turns: 10\n", luna_driver)
        self.assertIn("  web_search: disabled\n", luna_driver)
        self.assertIn("  timeout_seconds: 900\n", luna_driver)

        manifest = json.loads(
            (
                SIDECAR_ROOT / "efg_reachability_micro" / "run-manifest.json"
            ).read_text(encoding="utf-8")
        )
        self.assertEqual(manifest["schema_version"], "1.3.0")
        self.assertEqual(
            manifest["manifest_status"],
            "PUBLIC_STAGE_1A_LUNA_MANUAL_SMOKE_002_COMPLETED_SCORE_ONE_STAGE1_COMPLETE",
        )
        solver = manifest["solver"]
        self.assertEqual(solver["model"], "gpt-5.6-luna")
        self.assertEqual(solver["model_access_status"], "verified-by-access-smoke")
        self.assertEqual(solver["reasoning_effort"], "low")
        self.assertEqual(solver["max_turns"], 10)
        self.assertEqual(solver["timeout_seconds"], 900)
        self.assertEqual(solver["attempt_budget"], 1)
        self.assertEqual(solver["authentication_type"], "ChatGPT subscription")
        self.assertEqual(solver["model_verbosity"], "codex-default-unpinned")
        self.assertEqual(
            solver["model_verbosity_status"],
            "upstream-v0.2.0-driver-does-not-expose",
        )

        self.assertEqual(
            manifest["eve_budget"],
            {
                "max_iterations": 1,
                "phase2_workers": 1,
                "solver_examples_per_worker": 1,
                "optimizer_examples_per_worker": 1,
                "produced_optimizers": 1,
            },
        )
        artifacts = manifest["artifacts"]
        self.assertEqual(
            artifacts["luna_driver_sha256"], RUNNER._sha256(luna_driver_path)
        )
        self.assertEqual(
            artifacts["efg_top_level_config_sha256"],
            RUNNER._sha256(efg_config_path),
        )
        self.assertEqual(
            artifacts["sidecar_runner_sha256"],
            "3ba8621c205f965f2b5c6b4c66921f1ea1858127978d4948488f1e3129972cd1",
        )

        migration = manifest["configuration_migration"]
        self.assertEqual(migration["prompt_id"], "EVE-STAGE1-LUNA-CONFIG-MIGRATION-001")
        self.assertEqual(migration["prompt_version"], "1.0.0")
        self.assertEqual(migration["source_model"], "gpt-5.4-mini")
        self.assertEqual(migration["target_model"], "gpt-5.6-luna")
        self.assertEqual(migration["access_status"], "LUNA_ACCESS_SMOKE_PASSED")
        self.assertTrue(migration["configured_not_run"])
        self.assertEqual(
            migration["prompt_sha256"],
            RUNNER._sha256(SIDECAR_ROOT / "operator_prompts" / "STAGE1_LUNA_CONFIG_MIGRATION.md"),
        )
        self.assertEqual(
            migration["access_prompt_sha256"],
            RUNNER._sha256(SIDECAR_ROOT / "operator_prompts" / "STAGE1_LUNA_ACCESS_SMOKE.md"),
        )
        self.assertEqual(
            migration["access_jsonl_sha256"],
            "caec8d240df646ce2b42dfe1eba3c0788d1d5898f0df308b9687070ebeb4ca50",
        )
        self.assertEqual(
            migration["hooks_json_sha256"],
            "8c46e49b4512543d7809b7f8f16572c672ca8715c4e81f804aa7bb3ad7d385f6",
        )

        self.assertTrue(all(
            condition["model_status"] == "model-access-verified"
            for condition in manifest["conditions"]
        ))
        self.assertTrue(all(
            condition["paired_rng_status"] == "hard-disabled-unverified"
            for condition in manifest["conditions"]
        ))
        self.assertEqual(
            [condition["config_status"] for condition in manifest["conditions"]],
            [
                "hard-disabled-unverified",
                "hard-disabled-unverified",
                "manual-smoke-002-completed-score-one-stage1-complete",
            ],
        )
        blockers = " ".join(manifest["remaining_blockers"]).lower()
        for required in ("static", "fixed-guidance", "paired rng", "verbosity"):
            self.assertIn(required, blockers)
        self.assertTrue(all(
            "model access" not in condition["blocker"].lower()
            for condition in manifest["conditions"]
        ))

        execution = manifest["execution_record"]
        self.assertEqual(execution["status"], "completed-score-one-stage1-complete")
        self.assertTrue(execution["paid_or_model_execution"])
        self.assertTrue(execution["codex_exec_run"])
        self.assertTrue(execution["eve_runner_run"])
        self.assertEqual(execution["attempts"], 1)
        self.assertEqual(execution["codex_sessions"], 1)
        self.assertEqual(execution["candidate_score"], 1.0)
        self.assertFalse(execution["guidance_modified"])

        smoke = manifest["manual_smoke_001"]
        self.assertEqual(smoke["status"], "LUNA_EFG_MANUAL_SMOKE_COMPLETED")
        self.assertEqual(smoke["condition_id"], "EvE-evolved-guidance")
        self.assertEqual(smoke["eve_execute_attempts"], 1)
        self.assertEqual(smoke["codex_sessions"], 1)
        self.assertEqual(smoke["codex_resumes"], 0)
        self.assertEqual(smoke["observed_agent_turns"], 5)
        self.assertEqual(smoke["candidate_score"], 0.0)
        self.assertEqual(smoke["failure_codes"], ["compile-failed"])
        self.assertFalse(smoke["guidance_modified"])
        self.assertFalse(smoke["produced_optimizer"])

        smoke_002 = manifest["manual_smoke_002"]
        self.assertEqual(
            smoke_002["status"], "LUNA_EFG_MANUAL_SMOKE_002_COMPLETED"
        )
        self.assertEqual(smoke_002["condition_id"], "EvE-evolved-guidance")
        self.assertEqual(smoke_002["eve_execute_attempts"], 1)
        self.assertEqual(smoke_002["codex_sessions"], 1)
        self.assertEqual(smoke_002["codex_resumes"], 0)
        self.assertEqual(smoke_002["observed_agent_turns"], 5)
        self.assertEqual(smoke_002["candidate_score"], 1.0)
        self.assertEqual(smoke_002["gate_count"], 15)
        self.assertEqual(smoke_002["failure_codes"], [])
        self.assertFalse(smoke_002["guidance_modified"])
        self.assertFalse(smoke_002["produced_optimizer"])
        self.assertTrue(smoke_002["prior_run_unchanged"])

        history = manifest["execution_history"]
        self.assertEqual([item["candidate_score"] for item in history], [0.0, 1.0])
        self.assertEqual(
            [item["guidance_modified"] for item in history], [False, False]
        )

        repair = manifest["toolchain_feedback_repair"]
        self.assertEqual(repair["status"], "validated-no-model-call")
        self.assertEqual(repair["expected_lean_version"], "4.30.0")
        self.assertFalse(repair["upstream_modified"])
        self.assertEqual(repair["model_calls"], 0)

    def test_local_luna_access_report_matches_when_available(self) -> None:
        manifest = json.loads(
            (
                SIDECAR_ROOT / "efg_reachability_micro" / "run-manifest.json"
            ).read_text(encoding="utf-8")
        )
        migration = manifest["configuration_migration"]
        report_path = SIDECAR_ROOT.parents[1] / migration["access_report_path"]
        if not report_path.is_file():
            self.skipTest("sanitized local Luna access report is not available")

        self.assertEqual(RUNNER._sha256(report_path), migration["access_report_sha256"])
        report = json.loads(report_path.read_text(encoding="utf-8"))
        self.assertEqual(report["status"], "LUNA_ACCESS_SMOKE_PASSED")
        self.assertEqual(report["requested_model"], "gpt-5.6-luna")
        self.assertEqual(report["model_call"]["attempts"], 1)
        self.assertEqual(report["model_call"]["exit_code"], 0)
        self.assertTrue(report["model_call"]["agent_message_exact_match"])
        self.assertEqual(report["model_call"]["tool_event_count"], 0)
        self.assertTrue(report["postconditions"]["checkout_commit_unchanged"])
        self.assertTrue(report["postconditions"]["hooks_hash_unchanged"])
        self.assertFalse(report["eve_execute"])
        self.assertFalse(report["experiment_config_migrated"])

    def test_missing_checkout_error_is_concise_and_secret_free(self) -> None:
        with tempfile.TemporaryDirectory(prefix="eve-missing-checkout-") as raw_temp:
            stderr = io.StringIO()
            with mock.patch.dict(
                os.environ, {"EVE_TEST_SECRET": "do-not-leak-this-value"}
            ):
                with redirect_stderr(stderr):
                    result = RUNNER.main(
                        ["--eve-checkout", raw_temp, "--dry-run"]
                    )
            self.assertEqual(result, 2)
            message = stderr.getvalue()
            self.assertIn("EvE checkout is not a Git checkout", message)
            self.assertNotIn("do-not-leak-this-value", message)

    def test_score_direction_and_failure_scores_are_consistent(self) -> None:
        for case_path in (
            SIDECAR_ROOT / "smoke" / "case.json",
            SIDECAR_ROOT / "efg_reachability_micro" / "case.json",
        ):
            case = json.loads(case_path.read_text(encoding="utf-8"))
            score = case["score"]
            self.assertEqual(score["direction"], "higher-is-better")
            self.assertGreater(score["pass"], score["failure"])
            self.assertEqual(score["failure"], score["boundary_failure"])


if __name__ == "__main__":
    unittest.main()
