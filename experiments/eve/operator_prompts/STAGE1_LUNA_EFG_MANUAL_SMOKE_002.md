# Stage 1 Luna EFG post-toolchain-repair manual-smoke operator prompt

Prompt ID: `EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-002`

Version: `1.0.0`

Status: `FROZEN_NOT_RUN`

## Role and authorization

Act as the local experiment operator for the EconCSLib EVE sidecar. Run one
fresh, isolated, public Stage 1a EFG engineering smoke for exactly the
`EvE-evolved-guidance` condition with `gpt-5.6-luna`, after the solver-side
Lean toolchain feedback repair has passed non-model validation.

Receiving this frozen prompt as the active user task authorizes exactly one new
EvE `--execute` invocation. That invocation may consume ChatGPT subscription
quota and may launch exactly one Codex solver session with at most 10 agent
turns. It authorizes no retry, resume, import, prior-candidate reuse, fallback
model, second session, or second condition. Prompt 001 is permanently consumed;
this is a new protocol and not a retry under its budget. Merely generating,
reviewing, hashing, or freezing this prompt does not authorize execution.

## Goal and interpretation

Verify the same one-condition engineering path now that an isolated Codex HOME
can use the repository-selected, already-installed Lean 4.30 toolchain without
elan download fallback. Start again from the frozen public seed and initial
guidance; do not expose or import the candidate, transcript, population, or
workspace produced by manual smoke 001.

A coherent completed run may receive deterministic `score: 0.0` or
`score: 1.0`. Pipeline completion and candidate correctness are separate.
This remains a public engineering smoke and supports no benchmark,
model-capability, paired-condition, or EvE-improvement conclusion.

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
- EvE iterations/workers: 1 / 1
- Solver and optimizer examples per worker: 1 / 1
- Solver-session budget: one spawn, no resume
- Agent-turn limit: at most 10
- Boundary-repair attempts: 0
- Candidate attempt budget: 1
- Required Lean version: 4.30.0
- Existing completed run root, read-only historical evidence:
  `experiments/eve/.runtime/runs/20260820T101007_250550Z`
- New operator evidence root:
  `experiments/eve/.runtime/stage1-luna-efg-manual-smoke-002`
- New EvE output: exactly one additional timestamped directory under
  `experiments/eve/.runtime/runs/`

The sidecar resolves the repository-selected direct `lake` and `lean`
binaries using `elan which`, requires version 4.30.0, and prepends their shared
binary directory to the EvE process `PATH`. Codex still receives its isolated
HOME and Codex authentication shim. Do not set `HOME` or `ELAN_HOME` to the
user's real home, install a toolchain, update elan, or permit a network
fallback.

## Frozen evidence

- Manual-smoke-001 prompt SHA-256:
  `c2e431e56934c78c94a004d1b2b50932e89a0f53cae61869c006c61fdfe65a61`
- Manual-smoke-001 report SHA-256:
  `a9a22193fb0868e90201af5c157021cce5d349b80e3bacf59ca7158633ec0306`
- Post-run audit SHA-256:
  `4f9485272f993d1b2e09da7a954f65f4ecec7ea3c7df4c78a868c84e56d296e5`
- Sidecar runner SHA-256:
  `3ba8621c205f965f2b5c6b4c66921f1ea1858127978d4948488f1e3129972cd1`
- EFG run manifest SHA-256:
  `c6be9614696027830ccd85df10f2dab6e934746b58a4a0fde99802219af3fddd`
- EFG case contract SHA-256:
  `9eb842098a7f32016fb722108b36400cdb2323edce53463380f381c292191f05`
- Scoped Luna driver SHA-256:
  `bdb8ad69334ba97616586bf241853569ab60148b50830386c6294f5028e5f34d`
- EFG top-level config SHA-256:
  `9b81b19fe346c23c0a7cda10cbf6af740a9f246211ce8dab94e6fe9d54abda0f`
- EvE hooks SHA-256:
  `8c46e49b4512543d7809b7f8f16572c672ca8715c4e81f804aa7bb3ad7d385f6`

## Preconditions: no model call on failure

Before invoking `--execute`:

1. Read repository instructions, `experiments/eve/README.md`,
   `experiments/eve/READINESS.md`, this prompt and manifest entry, `case.json`,
   `run-manifest.json`, the sanitized manual-smoke-001 report, and its post-run
   audit. Do not read or copy the prior raw transcript or candidate into the
   new solver input.
2. Verify this prompt against `operator_prompts/manifest.json`. Require
   `FROZEN_NOT_RUN`, one authorized EvE attempt, one authorized Codex session,
   and only `EvE-evolved-guidance`.
3. Verify every frozen hash above, the exact EvE identity, hook trust, and both
   Git worktrees. Require the old run root to remain unchanged.
4. Require the audit status
   `MANUAL_SMOKE_001_AUDITED_TOOLCHAIN_FEEDBACK_REPAIRED`. Confirm prompt 001
   used exactly one attempt and cannot be resumed or retried.
5. Run all sidecar tests with the fixed checkout; require exactly 45 passes and
   zero skips/failures. The isolated solver HOME regression must compile the
   accepted EFG fixture, use Lean 4.30.0, and create no `.elan` directory in
   that temporary HOME.
6. Run the EFG sidecar `--check` and require
   `isolated solver Lean toolchain: available`, along with authentication,
   hooks, and locked dependencies. Run `--dry-run`; it must call no model.
7. Compose real Hydra config and reassert the fixed model, budgets,
   `resume_from=null`, `resume_iteration=null`, and `import_from=null`.
8. Snapshot existing run roots and both worktrees. Require the new operator
   evidence root to contain no prior attempt and no ambiguous partial new run.

If any precondition fails, do not invoke `--execute` and do not call a model.
Write a sanitized `BLOCKED_PRECONDITION` report with attempts `0` and stop.
Do not repair or loosen anything under this execution prompt.

## The one authorized execution

Create only the new operator evidence root, then run exactly once from the
EconCSLib repository root:

```bash
python3 experiments/eve/scripts/run.py \
  --eve-checkout /Users/lyuyuwei/Documents/eve-v0.2.0 \
  --experiment efg-reachability-micro \
  --acknowledge-model-quota \
  --execute
```

The shell may redirect outer stdout/stderr into the new operator evidence root
and record the exit code without changing command arguments. Resolve exactly
one additional timestamped run root from the launcher message and pre/post
snapshots.

Do not invoke `codex exec` directly, add Hydra overrides, or alter PATH/HOME in
the operator shell. Do not reuse the old run root, candidate, solver session,
population, checkpoint, cache, guidance output, or evaluation workspace.
Do not rerun after any result. Do not use static/fixed conditions or a fallback
model. One attempted `--execute` permanently exhausts this prompt.

## Post-run validation

1. Record the outer exit code, exactly one attempt, and exactly one additional
   run root; preserve the historical 001 root byte-for-byte.
2. For completion, require exactly one Codex spawn/session, zero resumes, no
   second condition, at most 10 observed agent turns, and checkpoint 1/1.
3. Verify resolved config, model, effort, web, budget, and null resume/import
   fields.
4. Inspect sanitized session evidence for solver Lean self-checks. Record the
   count and exit status of `lake env lean` commands if present. No self-check
   may report an elan download, installation request, missing toolchain,
   waiting lock, or isolated `.elan/toolchains` creation. If no solver
   self-check was attempted, record that fact without inventing one.
5. Require one produced solver evaluation and its deterministic score/gates.
   Score 0 alone is not an execution failure. Record whether guidance changed
   and whether an optimizer candidate was produced.
6. Hash checkpoint, config, runner log, lineage, telemetry, evaluation,
   candidate, token usage, and outer logs. Do not copy raw prompts or full
   transcripts into the sanitized report.
7. Recompute protected assets and confirm repository inputs, prior run,
   checkout commit, and hooks are unchanged. Only the new operator evidence
   root and exactly one additional EvE run root may persist.

Do not expose credentials, account data, request IDs, raw JSONL, raw session
transcripts, or unrelated dirty-file contents. Retained `model_cost_usd=0.0`
is not proof of zero billing; record actual cost as unknown unless an
authoritative account record is separately available.

## Status classification

Use exactly one status:

- `LUNA_EFG_MANUAL_SMOKE_002_COMPLETED`: the single command completed with one
  bounded session, one evaluation, checkpoint 1/1, intact boundaries, and no
  recurrence of the elan download/lock failure. Candidate score may be 0 or 1.
- `BLOCKED_PRECONDITION`: no execution or model call occurred.
- `FAILED_EXECUTION_NO_RETRY`: the consumed command failed at runtime.
- `FAILED_PROTOCOL`: session, condition, filesystem, prior-run, toolchain, or
  evidence boundaries were violated.
- `FAILED_UNCLASSIFIED_NO_RETRY`: a consumed attempt cannot be classified from
  sanitized evidence.

## Required report

Write
`experiments/eve/.runtime/stage1-luna-efg-manual-smoke-002/manual-smoke.json`
with the same evidence classes as report 001 plus:

```json
{
  "prompt_id": "EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-002",
  "status": "LUNA_EFG_MANUAL_SMOKE_002_COMPLETED | BLOCKED_PRECONDITION | FAILED_EXECUTION_NO_RETRY | FAILED_PROTOCOL | FAILED_UNCLASSIFIED_NO_RETRY",
  "execution": {
    "authorized_attempts": 1,
    "attempts": 0,
    "new_run_root_count": 0,
    "codex_spawn_count": 0,
    "codex_resume_count": 0,
    "distinct_session_count": 0,
    "observed_agent_turns": null
  },
  "solver_lean_feedback": {
    "preflight_isolated_compile_passed": false,
    "lake_env_lean_attempts": 0,
    "successful_attempts": 0,
    "elan_download_observed": false,
    "elan_lock_wait_observed": false,
    "isolated_elan_toolchain_created": false
  },
  "evaluation": {
    "completed": false,
    "score": null,
    "failure_codes": [],
    "guidance_modified": null,
    "produced_optimizer": null
  },
  "prior_run": {
    "run_root": "runs/20260820T101007_250550Z",
    "unchanged": false,
    "candidate_reused": false,
    "session_resumed": false,
    "population_imported": false
  }
}
```

For a blocked precondition, all attempt/session/root counts remain zero. Every
attempted command keeps attempts at one regardless of result.

## Stop rules

After validating the report, stop. Do not update prompts, manifests, README,
READINESS, configs, case assets, evaluator, seed, Lean library, or upstream.
Do not generate another prompt in the same execution task. The next step is a
separate post-run audit.
