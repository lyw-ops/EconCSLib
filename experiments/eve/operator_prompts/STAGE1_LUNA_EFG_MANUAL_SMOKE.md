# Stage 1 Luna EFG one-condition manual-smoke operator prompt

Prompt ID: `EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-001`

Version: `1.0.0`

Status: `FROZEN_NOT_RUN`

## Role and authorization

Act as the local experiment operator for the EconCSLib EVE sidecar. Run the
first fresh, isolated, public Stage 1a EFG engineering smoke for exactly the
`EvE-evolved-guidance` condition with `gpt-5.6-luna`.

Receiving this frozen prompt as the active user task authorizes exactly one
invocation of the EvE `--execute` command below. That invocation may consume
ChatGPT subscription quota and may launch exactly one Codex solver session
with at most 10 agent turns. It authorizes no retry, rerun, resume, import,
fallback model, second session, or second experimental condition. Merely
generating, reviewing, hashing, or freezing this prompt does not authorize its
execution.

## Goal and interpretation

Close the first real model-backed EvE path from the frozen EFG seed and
guidance through one solver/guidance rollout, the deterministic evaluator,
lineage persistence, telemetry, and checkpointing.

This is an engineering smoke, not a benchmark. A coherent completed run may
receive deterministic `score: 0.0` or `score: 1.0`; the score reports whether
the produced candidate passed the task gates, while smoke completion reports
whether the bounded pipeline executed and retained auditable evidence. Neither
outcome establishes model capability, EvE improvement, comparative guidance
quality, or readiness for the three-condition study.

## Fixed protocol

- EconCSLib fork: `/Users/lyuyuwei/Documents/EconCSlib`
- EvE checkout: `/Users/lyuyuwei/Documents/eve-v0.2.0`
- EvE tag/commit: `v0.2.0` / `50b2399258ab08b6225a87cd05bded9701caa23d`
- Task: `EVE-EFG-REACHABILITY-MICRO-001`
- Condition: `EvE-evolved-guidance` only
- Hydra experiment/config: `efg-reachability-micro` / `efg_reachability_micro`
- Model: `gpt-5.6-luna` exactly
- Reasoning effort: `low`
- Model verbosity: `codex-default-unpinned`
- Web search: disabled
- Model timeout: 900 seconds
- EvE iterations: 1
- Phase 2 workers: 1
- Solver examples per worker: 1
- Optimizer examples per worker: 1
- Produced optimizers: at most 1
- Solver-session budget: exactly 1 spawn, no resume
- Agent-turn limit inside that session: at most 10
- Boundary-repair attempts: 0
- Candidate attempt budget: 1
- Operator evidence root:
  `experiments/eve/.runtime/stage1-luna-efg-manual-smoke-001`
- Generated EvE root: exactly one new timestamped directory under
  `experiments/eve/.runtime/runs/`

The pinned `codex_exec` driver launches Codex with its own approvals/sandbox
bypass inside the generated solver workspace. Therefore this smoke relies on
the verified checkout identity, EvE hooks, the one-file candidate boundary,
the external deterministic evaluator, and pre/post filesystem evidence; do
not describe it as an OS sandbox or as a read-only model call.

The single solver session may edit `Candidate.lean` and the materialized
guidance tree that EvE exposes inside its generated workspace. Those are the
intended outputs of the evolved-guidance condition. It must not edit the
protected repository seed, evaluator, configs, prompts, manifests, Lean
library, or upstream checkout.

## Frozen evidence

- Configuration-migration prompt SHA-256:
  `1976419e5f2cd10dc7b8fa1ca9dcce39f7dcdafc2f1f989b11bf12a4fa5c1e16`
- Configuration-migration report:
  `experiments/eve/.runtime/stage1-luna-config-migration-001/config-migration.json`
- Configuration-migration report SHA-256:
  `1d54f57ad8fa653f4add99fec8d8ca4eb9eeabe171df175e4bd4c2b72a3ec129`
- Luna access report SHA-256:
  `dadb80549f0ebe61d4d969a9b6cf558428ae82310f618f452789a94b5b200d72`
- Scoped Luna driver SHA-256:
  `bdb8ad69334ba97616586bf241853569ab60148b50830386c6294f5028e5f34d`
- EFG top-level config SHA-256:
  `9b81b19fe346c23c0a7cda10cbf6af740a9f246211ce8dab94e6fe9d54abda0f`
- EFG run manifest SHA-256:
  `8e994d829c956414438a72899999f10ac38eeb649ae2130d1c73cab7fd16fabc`
- EFG case contract SHA-256:
  `856f4f15d4d915345d1a53b732e0f2e52d5eeb5e9f9bbd0cb7bf661edd9279cd`
- EvE hooks SHA-256:
  `8c46e49b4512543d7809b7f8f16572c672ca8715c4e81f804aa7bb3ad7d385f6`

## Preconditions: no model call on failure

Before invoking `--execute`:

1. Read repository instructions, `experiments/eve/README.md`,
   `experiments/eve/READINESS.md`, this prompt, its manifest entry, the EFG
   `case.json` and `run-manifest.json`, and the two sanitized Luna reports.
2. Verify this prompt against `operator_prompts/manifest.json`. Require the
   entry status `FROZEN_NOT_RUN`, `model_call_authorized=true`,
   `eve_execute_authorized=true`, one authorized EvE attempt, one authorized
   Codex session, and no authorization for another condition.
3. Verify every frozen hash above, the exact EvE commit/tag/remote identity,
   and the checkout's hook-trust status. Require no missing hook event.
4. Require access status `LUNA_ACCESS_SMOKE_PASSED` and migration status
   `LUNA_CONFIG_MIGRATION_READY`. Confirm their reports authorize neither a
   retry of their earlier work nor a different experiment.
5. Compose the real Hydra configuration through the pinned checkout and assert
   the fixed protocol values above, including `resume_from=null`,
   `resume_iteration=null`, `import_from=null`, one iteration, one worker, one
   spawn budget, 10-turn limit, zero boundary repairs, exact model, low effort,
   disabled web search, and 900-second timeout.
6. Run the complete sidecar tests with the fixed checkout; require exactly 42
   passes and zero skips/failures. Then run the EFG sidecar `--check` and
   `--dry-run`. Authentication, hooks, locked dependencies, fixture evaluator,
   and hashes must all pass without a model call.
7. Snapshot both Git worktrees and the set of existing entries under
   `.runtime/runs/` without printing unrelated dirty-file contents. Require
   that the fixed operator evidence root does not already contain an execution
   attempt and that no ambiguous partially created new run root exists.

If any precondition fails, do not invoke `--execute` and do not call a model.
Write a sanitized report with status `BLOCKED_PRECONDITION`, attempts `0`, and
stop. Do not repair, migrate, loosen, or regenerate any input under this prompt.

## The one authorized execution

Create only the fixed operator evidence root, then run the following command
exactly once from `/Users/lyuyuwei/Documents/EconCSlib`:

```bash
python3 experiments/eve/scripts/run.py \
  --eve-checkout /Users/lyuyuwei/Documents/eve-v0.2.0 \
  --experiment efg-reachability-micro \
  --acknowledge-model-quota \
  --execute
```

The shell may redirect the outer stdout and stderr into the fixed operator
evidence root and record the exit code, but it must not change the command
arguments. Parse the `Starting explicit EvE execution; artifacts: ...` line
and the pre/post directory snapshots to resolve exactly one newly created
timestamped EvE run root.

Do not invoke `codex exec` directly. Do not add another CLI option or Hydra
override. Do not rerun after timeout, rate limit, authentication failure, hook
failure, evaluator failure, malformed output, score 0, or any other result.
Do not call `resume`, set `resume_from`/`resume_iteration`/`import_from`, copy a
prior population, switch models, enable web search, raise budgets, or launch
the static/no-specialized-guidance or fixed-initial-guidance condition. One
attempted `--execute` invocation exhausts this prompt permanently, even if no
Codex session is successfully created.

## Post-run validation

After the command returns, inspect only sanitized facts from the fixed operator
evidence root and the one generated run root:

1. Record the outer exit code and verify that there was exactly one sidecar
   execution attempt and exactly one new generated run root.
2. For a completed run, require exactly one Codex spawn/session and no resume,
   no second provider session, no second condition, and no more than 10 agent
   turns. Record observed token/turn usage only when EvE retained it; never
   infer missing values.
3. Verify the resolved Hydra evidence still names `gpt-5.6-luna`, low effort,
   disabled web search, the fixed budgets, and null resume/import fields.
4. Verify `runner.log`, `checkpoint.json`, `solver_lineage.db`,
   `optimizer_lineage.db`, telemetry, solver/evaluation workspaces, and the
   deterministic score/evaluation evidence expected for a completed run.
   Record artifact paths relative to the run root and SHA-256 values; do not
   copy raw prompts or full transcripts into the sanitized report.
5. Require the final checkpoint to record one completed iteration. Require one
   produced solver evaluation. A score of 0 is valid evidence when the
   evaluator ran and retained its gate results; it is not a passing solution.
6. Recompute the protected case hashes and verify the source seed, evaluator,
   repository configs/prompts/manifests, EvE commit, and hooks are unchanged.
   Only the fixed operator evidence root and exactly one generated EvE run root
   may be new or modified by this task. Preserve unrelated pre-existing dirty
   work exactly as found.

Do not print or report credentials, account data, request IDs, authorization
headers, cookies, environment-variable values, raw Codex JSONL, raw session
transcripts, or unrelated dirty-file contents. Cost must remain `null` unless
the retained provider usage explicitly supplies it; do not invent a price for
subscription authentication or unpinned verbosity.

## Status classification

Use exactly one status:

- `LUNA_EFG_MANUAL_SMOKE_COMPLETED`: the one authorized command exited
  successfully, one session stayed within budget, one deterministic evaluation
  and final checkpoint are coherent, and all boundaries remained intact. This
  status is valid with candidate score 0 or 1.
- `BLOCKED_PRECONDITION`: a pre-call gate failed; attempts remain 0 and no model
  call or EvE execution occurred.
- `FAILED_EXECUTION_NO_RETRY`: the one authorized command was attempted but did
  not complete because of a normalized runtime, access, timeout, service, hook,
  or evaluator failure.
- `FAILED_PROTOCOL`: execution or retained evidence violated the one-root,
  one-session, turn, condition, filesystem, configuration, or reporting
  boundary.
- `FAILED_UNCLASSIFIED_NO_RETRY`: the consumed attempt cannot be safely placed
  in another sanitized class.

Never convert a failed attempt into `BLOCKED_PRECONDITION`, and never classify
score 0 alone as an execution failure.

## Required sanitized report

Write
`experiments/eve/.runtime/stage1-luna-efg-manual-smoke-001/manual-smoke.json`
with at least this shape:

```json
{
  "prompt_id": "EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-001",
  "prompt_version": "1.0.0",
  "status": "LUNA_EFG_MANUAL_SMOKE_COMPLETED | BLOCKED_PRECONDITION | FAILED_EXECUTION_NO_RETRY | FAILED_PROTOCOL | FAILED_UNCLASSIFIED_NO_RETRY",
  "recorded_at_utc": "RFC3339 timestamp",
  "task_id": "EVE-EFG-REACHABILITY-MICRO-001",
  "condition_id": "EvE-evolved-guidance",
  "model": "gpt-5.6-luna",
  "reasoning_effort": "low",
  "model_verbosity": "codex-default-unpinned",
  "budgets": {
    "eve_execute_attempts": 1,
    "iterations": 1,
    "workers": 1,
    "codex_sessions": 1,
    "agent_turn_limit": 10,
    "boundary_repairs": 0,
    "timeout_seconds": 900
  },
  "preconditions": {
    "prompt_hash_verified": false,
    "frozen_evidence_verified": false,
    "checkout_identity_verified": false,
    "hook_trust_verified": false,
    "hydra_protocol_verified": false,
    "tests_passed": false,
    "sidecar_check_passed": false,
    "dry_run_passed": false
  },
  "execution": {
    "authorized_attempts": 1,
    "attempts": 0,
    "exit_code": null,
    "run_root_relative": null,
    "new_run_root_count": 0,
    "codex_spawn_count": 0,
    "codex_resume_count": 0,
    "distinct_session_count": 0,
    "observed_agent_turns": null,
    "second_condition_observed": false
  },
  "evaluation": {
    "completed": false,
    "produced_solver_evaluations": 0,
    "score": null,
    "summary": null,
    "all_gates_passed": null
  },
  "artifacts": {
    "checkpoint_sha256": null,
    "runner_log_sha256": null,
    "solver_lineage_sha256": null,
    "optimizer_lineage_sha256": null,
    "telemetry_hashes": {},
    "evaluation_hashes": {},
    "outer_stdout_sha256": null,
    "outer_stderr_sha256": null
  },
  "usage": {
    "input_tokens": null,
    "cached_input_tokens": null,
    "output_tokens": null,
    "agent_turns": null,
    "model_cost_usd": null
  },
  "postconditions": {
    "protected_case_hashes_match": false,
    "checkout_commit_unchanged": false,
    "hooks_hash_unchanged": false,
    "tracked_experiment_inputs_unchanged": false,
    "writes_limited_to_two_runtime_roots": false
  },
  "remaining_blockers": [],
  "normalized_reason": ""
}
```

For `BLOCKED_PRECONDITION`, keep attempts, run-root count, and session counts at
0. For every attempted command, set attempts to exactly 1 regardless of exit
status. For `LUNA_EFG_MANUAL_SMOKE_COMPLETED`, require one run root, one spawn,
zero resumes, one distinct session, at most 10 observed turns, one evaluation,
and all postconditions true.

## Stop rules and final response

After validating the report, stop. Do not update the frozen solver prompt,
operator manifest, run manifest, README, READINESS, driver, config, case
contract, evaluator, seed, Lean library, or upstream EvE checkout. Do not
generate the next prompt in the same execution task.

Lead the final response with the exact status, whether the sole execution
attempt was consumed, and the deterministic candidate score if available.
Link the sanitized report and generated run root. State explicitly that only
the evolved-guidance condition ran and that static/fixed paired comparison,
RNG propagation, verbosity pinning, model-capability conclusions, and any Sol
replication remain blocked pending separate review.
