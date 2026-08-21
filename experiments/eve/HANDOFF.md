# EVE concise handoff

Last updated: 2026-08-21

## Repository checkpoint

- Local repository: `/Users/lyuyuwei/Documents/EconCSlib`
- Canonical handoff fork: <https://github.com/lyw-ops/EconCSLib>
- Experimental branch: `experiment/eve-stage5a`
- DEV-002 execution archive: `9269f3ea991e8e7e099dd541b870f37331796dc6`
- DEV-003 frozen-protocol handoff: this commit
- Long-term route authority: `experiments/eve/README.md`
- Current gate authority: `experiments/eve/READINESS.md`

Always verify the live branch, HEAD, upstream, remote, and worktree. The mixed
worktree contains extensive user-owned changes outside this task; preserve them
and stage only task-owned EVE files.

## Handoff policy

- Update this file after every completed task with scope, validation, execution
  status, blockers, and the next bounded action.
- Commit and push completed task-owned tracked work to the current experimental
  branch on the canonical handoff fork.
- Verify the pushed branch and commit before handoff. Ignored `.runtime`
  evidence remains local and must not be deleted or inferred from GitHub.
- Historical Stage 4, Stage 5A DEV-001, and DEV-002 inputs and runtime evidence
  are immutable. Do not repair, retry, resume, import, rewrite, or clean them.

## Historical baseline

- Stage 4 protocol `EVE-STAGE4-LUNA-ENTRY-GAME-DEV-002` completed all 12 cells
  and 24 Luna sessions. Direct success was static `1/2`, fixed `2/2`, evolved
  `2/2`; transport was static `1/2`, fixed `0/2`, evolved `0/2`. No evolved
  rollout produced an optimizer candidate, so Stage 4 did not demonstrate
  guidance evolution.
- Stage 5A DEV-001 was invalidated before execution with zero run roots and zero
  model sessions. Its checkpoint, detached identity, review, and findings are
  preserved.
- Stage 5A DEV-002 identity is
  `EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-002` version `2.0.0`, hash
  `6dafcb0d2476cd2f21df0c976f4f380488f1dcec067d7a0e7ba0802631045a05`.
  All 12 cells and 36 Luna sessions completed once, with no retry/resume/import.
  Four guidance candidates were produced and admitted; one direct/2718/evolved
  candidate was selected in two later iterations.
- DEV-002 is executed-but-defective. Its immutable checker used `datetime.UTC`
  under Python 3.9.6: all 36 sessions encountered the error, 91 invocations
  failed, and 25/36 rollouts retained an empty check list. The old auditor
  accepted empty lists. Preserve the raw outcomes and one local liveness chain,
  but do not call DEV-002 a clean comparison or use it to authorize Sol.

## Current Stage 5A DEV-003 state

The new protocol is
`EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-003`, version `3.0.0`, status
`FROZEN_NOT_YET_EXECUTED`, SHA-256
`4c407b3e654d4e38f6f35b48e924863b5a9ef72c1e6b9569996e86f00105ad49`.
The Codex AI plus deterministic review is
`stage5a_review/dev003-audit.json`; it is not independent human review.

DEV-003 is a wholly separate identity with new config/overlay assets, RNG
domain, fresh run-root parent, and fresh transactional attempt ledger. It does
not inherit DEV-002 population, guidance, candidates, sessions, roots, ledger,
or execution state.

The repair closes the known DEV-002 engineering defects:

- both immutable checker entrypoints are byte-identical and use
  `datetime.timezone.utc`, which compiles and runs under exact `/usr/bin/python3`
  3.9.6;
- safe preflight runs before formal root creation or ledger reservation in a
  disposable workspace with the exact execution Python, checker, Lean
  toolchain, and clean committed source, and verifies a real nonzero Lean exit,
  stdout/stderr evidence, and one hash-chained event;
- wrapper and auditor reject missing, empty, malformed, runtime/output/hash
  drift, final-candidate mismatch, and invalid evidence joins;
- an unvalidated failure flag cannot establish failure-derived guidance or
  liveness;
- ledger identity and frozen order reject DEV-002 reuse, duplicates, and
  out-of-order cells.

The Lean source boundary is the canonical fork at clean commit
`b490317186ef435670c2eeb16050a214cdbf9fe5`. The manifest recomputes a 109-file
closure from Git objects and excludes the mixed operator worktree. A separate
fresh clone at that commit, with exact clean pinned dependency checkouts,
verified the environment, built the frozen entry target, and ran the real
checker preflight.

## Last verified evidence

- 12 DEV-003 targeted tests passed.
- Full EVE suite: 87 tests passed; exactly two checkout-dependent tests skipped
  because unittest discovery supplied no explicit EvE checkout:
  `test_accepted_efg_fixture_compiles_in_isolated_solver_home` and
  `test_actual_hydra_loader_parses_both_configs_when_checkout_is_supplied`.
- Stage 4 local evidence verification and no-recheck audit passed.
- The immutable DEV-002 protocol verifier passed.
- DEV-003 detached protocol, frozen assets, committed Lean closure, dependency
  revisions, and clean-checkout environment verification passed.
- All 12 planned DEV-003 `--check` calls and all 12 `--dry-run` calls passed.
  Each check recorded an exact-runtime real Lean failure event.
- DEV-003 model calls, Luna sessions, quota consumed, `--execute` invocations,
  formal run roots, and formal ledger writes are all zero. DEV-002 state reuse
  or mutation is zero; its post-validation ledger SHA-256 remains
  `e593bf5726b20aa20f1cbb15882b7c2e9e169080233f346d67b48d6543a37922`.

These facts establish review-ready protocol engineering only. DEV-003 has
produced, admitted, or selected no guidance. They establish no clean condition
comparison, causal EvE effect, model capability, benchmark readiness,
evaluation completion, independent human review, or Sol readiness.

## Next bounded action and stop condition

Stop at DEV-003 `FROZEN_NOT_YET_EXECUTED`. Do not invoke `--execute`, add
`--acknowledge-model-quota`, consume Luna quota, retry DEV-002, or start Sol.
The next action requires a separate explicit user authorization for the frozen
DEV-003 12-cell Luna matrix. Preparation and review do not imply that authority.

## Local versus GitHub evidence

GitHub stores the tracked protocols, code, reviews, documentation, and commit
history. Runtime evidence under `experiments/eve/.runtime/` is ignored and
remains only on this machine. A fresh clone cannot reconstruct historical
Stage 4/DEV-002 transcripts, but their tracked audit hashes remain authoritative
summaries. DEV-003 reproducibility is different: its Lean environment is tied
to a clean committed source tree rather than the user's uncommitted Lean work.

## Bootstrap prompt for the next conversation

```text
Open /Users/lyuyuwei/Documents/EconCSlib on experiment/eve-stage5a. Read the
root and experiments/eve AGENTS.md files, then read experiments/eve/HANDOFF.md,
README.md, READINESS.md, stage5a_review/dev002-execution-audit.json, and
stage5a_review/dev003-audit.json. Inspect the live branch, remotes, worktree,
and pushed commit. Preserve all unrelated user changes and all Stage 4,
DEV-001, and DEV-002 historical evidence.

DEV-001 is invalidated-before-execution. DEV-002 executed 12 cells/36 Luna
sessions but is permanently executed-defective because its Python-3.9 checker
failed and the auditor accepted empty evidence; do not retry or repair it.
DEV-003 is EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-003 v3.0.0, hash
4c407b3e654d4e38f6f35b48e924863b5a9ef72c1e6b9569996e86f00105ad49,
and is frozen review-ready but not executed. It uses the clean committed Lean
source b490317186ef435670c2eeb16050a214cdbf9fe5 and fresh state.

Do not execute DEV-003, consume Luna quota, or start Sol unless the user gives
new explicit authorization. If authorized, follow only the frozen matrix/order
and fail-closed launcher; otherwise remain in read-only review mode. Update
HANDOFF, stage only task-owned files, commit, push to fork/experiment/eve-stage5a,
and verify the remote after every completed task.
```
