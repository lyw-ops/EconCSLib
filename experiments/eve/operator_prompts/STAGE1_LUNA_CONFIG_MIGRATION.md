# Stage 1 Luna configuration-migration operator prompt

Prompt ID: `EVE-STAGE1-LUNA-CONFIG-MIGRATION-001`

Version: `1.0.0`

Status: `FROZEN_NOT_RUN`

## Role and authorization

Act as the local configuration operator for the EconCSLib EVE sidecar. Migrate
only the public Stage 1a EFG micro-pilot from its unverified `gpt-5.4-mini`
plan to the already access-verified explicit model `gpt-5.6-luna`.

Receiving this prompt as the active user task authorizes the bounded local file
edits and non-model validation listed below. It authorizes no model call, no
`codex exec`, no EvE runner, no `--execute`, and no Lean solver task.

## Goal

Produce a reviewable, hash-anchored Luna configuration for the first future
one-condition EFG engineering smoke while preserving historical Stage 0
configuration, all experiment budgets, and every still-unverified blocker.

This task configures a future run; it does not perform that run and cannot
establish model capability, EFG correctness, or an EvE improvement.

## Fixed evidence and target

- EconCSLib fork: `/Users/lyuyuwei/Documents/EconCSlib`
- EvE checkout: `/Users/lyuyuwei/Documents/eve-v0.2.0`
- EvE commit: `50b2399258ab08b6225a87cd05bded9701caa23d`
- Requested model: `gpt-5.6-luna` exactly; do not use the `gpt-5.6` alias
- Stage 1 engineering reasoning effort: `low`
- Access-smoke prompt: `EVE-STAGE1-LUNA-ACCESS-SMOKE-001` v1.0.0
- Access-smoke prompt SHA-256:
  `4395ff4f8d1ecbf7c8b6fa1d3977d1e4f696b4cc9abd9850124728c1de39ab6f`
- Access-smoke report:
  `experiments/eve/.runtime/stage1-luna-access-smoke-001/access-smoke.json`
- Access-smoke report SHA-256:
  `dadb80549f0ebe61d4d969a9b6cf558428ae82310f618f452789a94b5b200d72`
- Access-smoke JSONL SHA-256:
  `caec8d240df646ce2b42dfe1eba3c0788d1d5898f0df308b9687070ebeb4ca50`
- Hooks SHA-256:
  `8c46e49b4512543d7809b7f8f16572c672ca8715c4e81f804aa7bb3ad7d385f6`
- Output root:
  `experiments/eve/.runtime/stage1-luna-config-migration-001`

The official model guidance records `gpt-5.6-luna` as the efficient GPT-5.6
tier and recommends setting reasoning effort intentionally. Codex accepts
`model_reasoning_effort = "low"`; the pinned EvE v0.2.0 `codex_exec` adapter
passes model and reasoning effort but does not expose `model_verbosity`.

## Preconditions

Before editing any file:

1. Read repository instructions, `experiments/eve/README.md`,
   `experiments/eve/READINESS.md`, this prompt, its manifest entry, the EFG
   run manifest, active Hydra configs, and the sanitized access-smoke report.
2. Verify this prompt's SHA-256 against `operator_prompts/manifest.json`.
3. Verify the access report and referenced prompt/JSONL hashes. Require status
   `LUNA_ACCESS_SMOKE_PASSED`, requested model `gpt-5.6-luna`, attempts `1`,
   exit code `0`, exact-message match, zero tool events, unchanged checkout and
   hook identities, `eve_execute=false`, and `experiment_config_migrated=false`.
4. Verify the EvE checkout identity and hooks hash, then run the existing EFG
   sidecar `--check`. Authentication, hook trust, and the locked environment
   must all be available.
5. Snapshot the allowed target files and both Git worktrees without printing
   unrelated dirty-file contents. If an allowed existing file changed after
   this prompt was frozen in a way that conflicts with the contract, stop.

If any precondition fails, make no configuration edit. Write a sanitized
`BLOCKED_PRECONDITION` report and stop.

## Allowed repository changes

Only these paths may be created or edited:

- `experiments/eve/configs/eve/driver/codex_luna_offline.yaml` (new)
- `experiments/eve/configs/eve/efg_reachability_micro.yaml`
- `experiments/eve/efg_reachability_micro/run-manifest.json`
- `experiments/eve/tests/test_scaffold.py`
- `experiments/eve/README.md`
- `experiments/eve/READINESS.md`

The runtime report may be written only under the fixed output root. Do not edit
this prompt, `operator_prompts/manifest.json`, the legacy
`driver/codex_offline.yaml`, any application/optimizer/evaluation/loop/runtime
config, evaluator, seed, fixture, overlay, Lean file, upstream checkout, user
Codex configuration, credentials, or hook definition.

## Required migration

### 1. Add a scoped Luna driver

Create `codex_luna_offline.yaml` by preserving the existing driver contract and
changing only the explicit model identity:

```yaml
# @package _global_

driver:
  driver: codex_exec
  executable: codex
  model: gpt-5.6-luna
  reasoning_effort: low
  rollout_max_turns: 10
  web_search: disabled
  timeout_seconds: 900
  overrides:
    solver:
      reasoning_effort: low
```

Do not add guessed fields, prices, provider settings, API keys, service tiers,
profiles, fallbacks, or `model_verbosity`. The pinned adapter does not consume
`model_verbosity`; silently adding it would create a false reproducibility
claim. Record verbosity as Codex-default/unpinned in the run manifest instead.

### 2. Scope the new driver to the EFG micro-pilot

Change only the EFG top-level Hydra default from `driver: codex_offline` to
`driver: codex_luna_offline`. Leave the Mathlib-style Stage 0 config and legacy
driver unchanged so historical and future protocol identities remain distinct.

### 3. Migrate the unexecuted EFG run manifest

Update `efg_reachability_micro/run-manifest.json` as a new unexecuted protocol:

- set `schema_version` to `1.1.0`;
- set `manifest_status` to
  `PUBLIC_STAGE_1A_LUNA_MANUAL_SMOKE_CONFIGURED_NOT_RUN`;
- set `solver.model` to `gpt-5.6-luna` and
  `solver.model_access_status` to `verified-by-access-smoke`;
- retain `reasoning_effort=low`, turn/timeout/attempt budgets, authentication
  type, EvE budget, environment identity, shared controls, task ID, and seed ID;
- add `solver.model_verbosity="codex-default-unpinned"` and
  `solver.model_verbosity_status="upstream-v0.2.0-driver-does-not-expose"`;
- add a `configuration_migration` object recording this prompt ID/version,
  source model, target model, access prompt/report paths and fixed hashes,
  access status, and `configured_not_run=true`;
- add SHA-256 entries for the new Luna driver and changed EFG top-level config;
- set every condition's `model_status` to `model-access-verified` without
  changing its config or paired-RNG status;
- remove only the now-resolved model-access clause from blocker text. Static,
  fixed-guidance, paired RNG, and any verbosity blocker remain explicit;
- preserve `execution_record.status="not-run"`,
  `paid_or_model_execution=false`, `codex_exec_run=false`, and
  `eve_runner_run=false`; add a scope note that this record covers the EFG
  experiment and excludes the separate completed access smoke.

Do not rewrite the historical baseline commit or dirty-worktree statement.
Do not claim the three-condition study is configured, paired, reproducible, or
ready. A default/unpinned verbosity is acceptable only for the first public
one-condition engineering smoke, not for comparative or formal results.

### 4. Add deterministic structural coverage

Extend `test_scaffold.py` to verify, without a model call:

- the legacy Stage 0 driver remains `gpt-5.4-mini`;
- the EFG config selects `codex_luna_offline` and the new driver specifies
  exactly `gpt-5.6-luna`, low effort, ten turns, disabled web search, and the
  existing timeout;
- real Hydra composition through the pinned checkout resolves those values;
- the run manifest is v1.1.0, hash-anchors the active driver/config and access
  evidence, marks access verified, preserves all budgets and not-run facts,
  and leaves static/fixed/paired-RNG blockers enabled;
- no active EFG config or run-manifest model field contains `gpt-5.4-mini` or
  the ambiguous `gpt-5.6` alias.

Do not make tests depend on raw JSONL/stderr contents. They may verify the
sanitized report and fixed hashes only when the local ignored artifact exists;
otherwise skip the local-evidence assertion rather than weakening repository
structure checks.

### 5. Update status documentation

Update README's authoritative route and READINESS to say:

- the EFG Luna driver/run manifest is configured but not run;
- the access gate is complete and its one-turn budget remains spent;
- verbosity, static/fixed semantics, and paired RNG are still unverified;
- the next separately authorized gate is the first fresh, isolated,
  one-condition EFG manual smoke;
- no EvE runner, `--execute`, or Lean solver task was run by this migration.

Increase the README route version and test count only if the corresponding
changes and complete test result are real. Preserve earlier changelog entries.

## Validation without model execution

Run all of the following after editing:

1. JSON syntax validation for both manifests.
2. YAML/Hydra composition for both top-level configs through the pinned EvE
   environment; assert the EFG driver values and unchanged Stage 0 values.
3. The complete `experiments/eve/tests` suite with
   `EVE_V020_TEST_CHECKOUT` set to the fixed checkout.
4. EFG sidecar `--check` and `--dry-run` only.
5. SHA-256 recomputation for every changed/fixed artifact recorded in the
   manifests.
6. Pre/post checkout identity, hook hash, and repository-boundary comparison.

Use the sidecar's isolated uv cache behavior. If an outer filesystem sandbox
blocks Lean evaluator temporary writes, record that restriction and rerun the
same tests under normal authorized local repository permissions; do not change
the evaluator or weaken tests to accommodate the outer sandbox.

## Success and failure states

Use exactly one status:

- `LUNA_CONFIG_MIGRATION_READY`: all required edits and validations pass;
- `BLOCKED_PRECONDITION`: no edit occurred because an input gate failed;
- `FAILED_VALIDATION`: edits were attempted but a required check failed and
  the result was not misrepresented as ready.

Do not repair or alter upstream EvE, trust, authentication, model access,
static/fixed semantics, paired RNG, or formal-pilot blockers in this task.

## Required report

Write
`experiments/eve/.runtime/stage1-luna-config-migration-001/config-migration.json`
with this minimum shape:

```json
{
  "prompt_id": "EVE-STAGE1-LUNA-CONFIG-MIGRATION-001",
  "prompt_version": "1.0.0",
  "status": "LUNA_CONFIG_MIGRATION_READY | BLOCKED_PRECONDITION | FAILED_VALIDATION",
  "recorded_at_utc": "RFC3339 timestamp",
  "source_model": "gpt-5.4-mini",
  "target_model": "gpt-5.6-luna",
  "reasoning_effort": "low",
  "preconditions": {
    "prompt_hash_verified": false,
    "access_evidence_verified": false,
    "checkout_identity_verified": false,
    "hook_trust_verified": false,
    "sidecar_check_passed": false
  },
  "changes": {
    "new_scoped_driver": false,
    "efg_driver_selected": false,
    "run_manifest_migrated": false,
    "legacy_stage0_unchanged": false,
    "documentation_updated": false
  },
  "validation": {
    "json_valid": false,
    "hydra_composition_passed": false,
    "tests_passed": false,
    "test_count": 0,
    "sidecar_check_passed": false,
    "dry_run_passed": false,
    "artifact_hashes_match": false
  },
  "artifact_hashes": {
    "operator_prompt_sha256": "",
    "luna_driver_sha256": "",
    "efg_top_level_config_sha256": "",
    "run_manifest_sha256": "",
    "access_report_sha256": ""
  },
  "remaining_blockers": [],
  "model_calls": 0,
  "codex_exec": false,
  "eve_execute": false,
  "eve_runner_run": false,
  "lean_solver_task_run": false
}
```

Do not include raw logs, credentials, environment values, account data, or
unrelated dirty-file contents. The report itself is not authorization for the
next run.

## Stop and final response

Stop after validating the report. Do not start the manual smoke or generate
another execution prompt.

Lead the final response with the exact migration status. Link the report and
the changed config/manifest files, state the test result, list the remaining
blockers, and state explicitly that model calls, `codex exec`, EvE execution,
and Lean solver execution were all zero for this task.
