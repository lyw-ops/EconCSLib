# Stage 1 Luna preflight operator prompt

Prompt ID: `EVE-STAGE1-LUNA-PREFLIGHT-001`

Version: `1.0.0`

Status: `FROZEN_NOT_RUN`

## Role

Act as the local experiment operator for the EconCSLib EVE sidecar. Establish
whether this machine is ready for a separately authorized first Luna manual
smoke. This is a preflight and evidence-collection task, not a solver run.

## Goal

Verify the frozen repository assets, the explicit EvE v0.2.0 checkout, local
dependencies, Hydra composition, safe launcher behavior, Codex authentication,
and the remaining exact blockers without invoking an EvE runner or a model.

## Inputs

- EconCSLib fork: `/Users/lyuyuwei/Documents/EconCSlib`
- Required checkout placeholder: `<ABSOLUTE_EVE_V0_2_0_CHECKOUT>`
- Experiment: `efg-reachability-micro`
- Intended future solver model: `gpt-5.6-luna`
- Frozen solver prompt: `EVE-EFG-SOLVER-PROMPT-001` v1.0.0
- Accepted manual candidate record:
  `experiments/eve/.runtime/manual-stage1-efg-reachability-001/run-record.json`

Replace the checkout placeholder only with an existing, explicit absolute path.
If no such checkout has been supplied, do not guess or search the whole home
directory; report `BLOCKED_MISSING_PINNED_CHECKOUT`.

## Success criteria

- The repository seed, prompt, evaluator, configuration, and protected hashes
  match their frozen contracts.
- The supplied checkout matches every identity in `UPSTREAM.lock.json`,
  including origin, tag object, peeled commit, license, notice, runtime files,
  and Python version.
- The locked upstream environment is already present and the real Hydra loader
  can compose the EFG configuration.
- All local EVE tests pass, except the documented checkout-dependent skip when
  no checkout is supplied.
- The accepted fixture receives `score: 1.0`; declared negative fixtures remain
  rejectable under the existing test suite.
- `--check` and `--dry-run` complete without invoking Codex, a model, network,
  or the EvE runner.
- Codex authentication status is checked without printing credentials.
- The report distinguishes authentication from exact Luna model access; model
  access remains unverified until a separately authorized minimal model call.

## Safety and scope

Outside `experiments/eve/.runtime/stage1-luna-preflight-001/`, perform read-only
inspection. Do not modify the seed, solver prompt, evaluator, configs,
`UPSTREAM.lock.json`, run manifest, Lean source, or any other protected asset.

Do not run `--execute`, `codex exec`, an EvE runner, a model availability
prompt, `git clone`, `git pull`, `uv sync`, dependency installation, or any
network command. Do not expose tokens, cookies, environment-variable values,
account identifiers, or unrelated dirty-worktree content. Do not change the
configured `gpt-5.4-mini` alias during this preflight; record that migration to
`gpt-5.6-luna` is still pending.

## Required checks

1. Read the repository `AGENTS.md`, `experiments/eve/README.md`,
   `experiments/eve/READINESS.md`, `UPSTREAM.lock.json`, the EFG `case.json`,
   and the accepted manual run record.
2. Confirm the restored seed hash is
   `ef72862105a73cbdc3911f054295479e5caa048780bffa3e6f1c27b755d77231`
   and the solver prompt hash is
   `e87b99b7b67183062962d8c0fcddb362373642eaed84339564c1cc294fbb2bb2`.
3. Run the complete local EVE unit test suite.
4. If and only if an explicit checkout path is supplied, run:

   ```bash
   python3 experiments/eve/scripts/run.py \
     --eve-checkout <ABSOLUTE_EVE_V0_2_0_CHECKOUT> \
     --experiment efg-reachability-micro \
     --check

   python3 experiments/eve/scripts/run.py \
     --eve-checkout <ABSOLUTE_EVE_V0_2_0_CHECKOUT> \
     --experiment efg-reachability-micro \
     --dry-run

   python3 experiments/eve/scripts/run.py \
     --eve-checkout <ABSOLUTE_EVE_V0_2_0_CHECKOUT> \
     --experiment efg-reachability-micro \
     --evaluate-fixture accepted
   ```

5. Run `codex login status` only as a credential-free authentication check.
   Do not infer that successful login proves access to `gpt-5.6-luna`.
6. Write a sanitized report to
   `experiments/eve/.runtime/stage1-luna-preflight-001/preflight.json` with:

   ```json
   {
     "prompt_id": "EVE-STAGE1-LUNA-PREFLIGHT-001",
     "status": "READY_FOR_SEPARATE_MODEL_ACCESS_SMOKE | BLOCKED_*",
     "checkout_identity": "verified | missing | invalid",
     "dependencies": "verified | missing | not_checked",
     "tests": "passed | failed",
     "check": "passed | failed | not_run",
     "dry_run": "passed | failed | not_run",
     "accepted_fixture": "passed | failed | not_run",
     "codex_auth": "available | unavailable | not_checked",
     "luna_model_access": "unverified",
     "model_config_migration": "pending",
     "blockers": [],
     "commands": [],
     "exit_codes": {},
     "artifact_hashes": {}
   }
   ```

Record sanitized commands and exit codes, not full environment dumps or
credential-bearing output.

## Stop rules

On a missing checkout, identity mismatch, absent locked environment, failed
hard gate, or unavailable Codex authentication, stop after recording the exact
blocker. Do not repair, install, clone, migrate the model configuration, or
continue toward execution in this prompt.

Stop successfully at `READY_FOR_SEPARATE_MODEL_ACCESS_SMOKE`. This status does
not authorize a model call and is not evidence of Luna capability or EvE gain.

## Final response

Lead with the readiness status. Link the sanitized preflight report, list only
material blockers, and state the smallest authorized next action. Do not claim
that Luna access or the EFG experiment has been executed.
