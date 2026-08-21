# Stage 1 Luna access-smoke operator prompt

Prompt ID: `EVE-STAGE1-LUNA-ACCESS-SMOKE-001`

Version: `1.0.0`

Status: `FROZEN_NOT_RUN`

## Role

Act as the local experiment operator for the EconCSLib EVE sidecar. Perform one
minimal, bounded Codex access smoke for the exact model `gpt-5.6-luna`. This is
an account/model routing check, not a Lean solver run and not an EvE run.

Receiving this prompt as the active user task authorizes exactly one model turn
through the command specified below. It authorizes no retry and no other model
call. Merely generating, reviewing, or freezing this prompt does not authorize
its execution.

## Goal

Determine whether the current saved Codex authentication can successfully
complete one explicit `gpt-5.6-luna` request while preserving the verified EvE
hook boundary. Produce a sanitized, reproducible access record without
exposing credentials or changing experiment configuration.

## Fixed inputs

- EconCSLib fork: `/Users/lyuyuwei/Documents/EconCSlib`
- EvE checkout: `/Users/lyuyuwei/Documents/eve-v0.2.0`
- EvE commit: `50b2399258ab08b6225a87cd05bded9701caa23d`
- Preflight report:
  `/Users/lyuyuwei/Documents/EconCSlib/experiments/eve/.runtime/stage1-luna-preflight-001/preflight.json`
- Requested model: `gpt-5.6-luna`
- Reasoning effort: `low`
- Model verbosity: `low`
- Model-turn budget: exactly `1`
- Expected final agent message: `EVE_LUNA_ACCESS_OK`
- Output root:
  `/Users/lyuyuwei/Documents/EconCSlib/experiments/eve/.runtime/stage1-luna-access-smoke-001`

Do not substitute `gpt-5.6`, `gpt-5.6-sol`, `gpt-5.6-terra`, or any fallback.
Do not infer account-specific access from public model documentation; only the
explicit command result below can establish this local access gate.

## Preconditions

Before any model call:

1. Read repository instructions plus `experiments/eve/README.md`,
   `experiments/eve/READINESS.md`, this prompt's manifest entry, and the
   preflight report.
2. Confirm the preflight status is `READY_FOR_SEPARATE_MODEL_ACCESS_SMOKE`,
   `codex_hook_trust` is `verified`, `hook_trust.missing_events` is empty,
   `model_execution` is `false`, and `eve_execute` is `false`.
3. Confirm the EvE checkout still resolves to the fixed commit and its
   generated `.codex/hooks.json` SHA-256 is
   `8c46e49b4512543d7809b7f8f16572c672ca8715c4e81f804aa7bb3ad7d385f6`.
4. Run the existing EFG sidecar `--check`. It must report Codex authentication,
   hook trust, and the locked upstream environment as available.
5. Read `codex exec --help` without invoking a model and confirm the installed
   CLI supports `--model`, `--sandbox`, `--ephemeral`, `--json`, `--cd`, and
   `--config`.

If any precondition fails, make no model call. Write the sanitized report with
status `BLOCKED_PRECONDITION` and stop.

## The one authorized model call

Create only the output root above, then run the following command exactly once
from the EconCSLib repository root. Capture stdout as JSONL and stderr as a
local ignored runtime artifact. Do not print either stream wholesale.

```bash
codex exec \
  --cd /Users/lyuyuwei/Documents/eve-v0.2.0 \
  --model gpt-5.6-luna \
  --sandbox read-only \
  --ephemeral \
  --json \
  --color never \
  --config 'model_reasoning_effort="low"' \
  --config 'model_verbosity="low"' \
  --config 'agents.enabled=false' \
  'Do not call tools, read files, inspect the repository, access the web, or modify state. Reply with exactly EVE_LUNA_ACCESS_OK and no other text.'
```

The shell invocation may redirect the two streams into the output root and
record the exit code, but it must not alter the command arguments. Do not add
`--dangerously-bypass-hook-trust`, `--dangerously-bypass-approvals-and-sandbox`,
`--ignore-user-config`, `--ignore-rules`, `--skip-git-repo-check`, a profile,
an API key, or any fallback model.

Do not rerun the command for a timeout, rate limit, authentication failure,
model-unavailable error, malformed output, hook failure, or any other result.
One attempted turn exhausts this prompt's entire model budget.

## Success criteria

Classify the smoke as `LUNA_ACCESS_SMOKE_PASSED` only if all of the following
hold:

- the command was attempted exactly once and exited with status `0`;
- stdout is valid JSONL with one `turn.started` and one `turn.completed`, and no
  `turn.failed` or top-level `error` event;
- the sole final agent-message text is exactly `EVE_LUNA_ACCESS_OK` after only
  surrounding whitespace is removed;
- there is no command-execution, file-change, MCP-call, web-search, image,
  browser, subagent, or other tool-use event;
- the checkout commit and hook hash still match their pre-call values;
- no file in either Git checkout outside the designated runtime output root was
  created or changed relative to the pre-call repository snapshots; unrelated
  pre-existing dirty state, if any, is unchanged.

A pass verifies only that this local Codex authentication accepted and
completed the explicit Luna request. It is not evidence of Lean ability, EFG
correctness, EvE improvement, benchmark quality, deterministic model behavior,
or suitability of a reasoning-effort setting.

## Failure classification

Use exactly one sanitized status when the smoke does not pass:

- `BLOCKED_PRECONDITION`: a required pre-call gate failed, so no call occurred;
- `BLOCKED_LUNA_MODEL_ACCESS`: the single request was rejected for model or
  account access;
- `FAILED_TRANSIENT_NO_RETRY`: the single request encountered a rate, service,
  transport, or timeout failure;
- `FAILED_PROTOCOL`: the command ran but the output, event boundary, hook
  boundary, or filesystem boundary violated this protocol;
- `FAILED_UNCLASSIFIED_NO_RETRY`: the result cannot be safely classified from
  sanitized evidence.

Do not include raw server messages, request IDs, account identifiers, tokens,
cookies, authorization headers, environment-variable values, or credential
paths in the report. Record only a short normalized reason category.

## Required report

Write
`experiments/eve/.runtime/stage1-luna-access-smoke-001/access-smoke.json`
with this shape:

```json
{
  "prompt_id": "EVE-STAGE1-LUNA-ACCESS-SMOKE-001",
  "prompt_version": "1.0.0",
  "status": "LUNA_ACCESS_SMOKE_PASSED | BLOCKED_PRECONDITION | BLOCKED_LUNA_MODEL_ACCESS | FAILED_TRANSIENT_NO_RETRY | FAILED_PROTOCOL | FAILED_UNCLASSIFIED_NO_RETRY",
  "recorded_at_utc": "RFC3339 timestamp",
  "requested_model": "gpt-5.6-luna",
  "reasoning_effort": "low",
  "model_verbosity": "low",
  "codex_cli": "version only",
  "authentication_type": "saved Codex authentication; credential values not inspected",
  "preconditions": {
    "preflight_ready": false,
    "checkout_identity_verified": false,
    "hook_trust_verified": false,
    "sidecar_check_passed": false
  },
  "model_call": {
    "authorized_budget": 1,
    "attempts": 0,
    "exit_code": null,
    "jsonl_valid": false,
    "turn_started_count": 0,
    "turn_completed_count": 0,
    "turn_failed_count": 0,
    "error_event_count": 0,
    "agent_message_exact_match": false,
    "tool_event_count": 0,
    "usage": {
      "input_tokens": null,
      "cached_input_tokens": null,
      "output_tokens": null,
      "reasoning_output_tokens": null
    }
  },
  "postconditions": {
    "checkout_commit_unchanged": false,
    "hooks_hash_unchanged": false,
    "repository_writes_outside_runtime_root": false
  },
  "artifact_hashes": {
    "operator_prompt_sha256": "",
    "hooks_json_sha256": "",
    "jsonl_sha256": "",
    "stderr_sha256": ""
  },
  "normalized_reason": "",
  "eve_execute": false,
  "experiment_config_migrated": false
}
```

Record token counts only when present in the successful JSONL completion event.
Hash raw artifacts without copying their contents into the report. A blocked
precondition keeps attempts at `0`; every attempted command keeps attempts at
exactly `1`, regardless of outcome.

## Safety and scope

- Within the EconCSLib and EvE Git checkouts, operate read-only outside the
  designated runtime output root. Compare pre/post repository snapshots without
  printing unrelated dirty-file contents.
- Do not run `--execute`, the EvE runner, a Lean solver task, fixture evaluation,
  a second `codex exec`, or any other model call.
- Do not edit the driver, Hydra configs, run manifest, solver prompt, evaluator,
  Lean files, README, READINESS, this prompt, or its manifest.
- Do not install, update, clone, pull, fetch, browse, or search the web.
- Do not inspect or print authentication files, environment variables, tokens,
  cookies, headers, account identifiers, or billing details.
- Do not claim that a successful call is free; it may consume account quota or
  incur charges under the user's configured authentication and plan.

## Stop rules

Stop immediately after writing and validating the sanitized report. Do not
repair a failure, change trust, change authentication, select a fallback model,
migrate configuration, or begin an EFG/EvE run.

On success, the next separately reviewed task is model/config manifest
migration under a new protocol version. On failure, the next task is a
credential-free diagnosis based only on the normalized category.

## Final response

Lead with the exact status and whether the single model-call budget was used.
Link the sanitized report. State that no EvE runner or experiment execution was
performed and that configuration remains unmigrated. Do not paste raw JSONL or
stderr.
