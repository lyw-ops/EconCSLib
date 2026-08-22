# EVE concise handoff

Last updated: 2026-08-23

## Repository checkpoint

- Local repository: `/Users/lyuyuwei/Documents/EconCSlib`
- Canonical handoff fork: <https://github.com/lyw-ops/EconCSLib>
- Experimental branch: `experiment/eve-stage5a`
- DEV-002 execution archive: `9269f3ea991e8e7e099dd541b870f37331796dc6`
- DEV-003 frozen-protocol handoff: `3517eeba2f48ff2ad8fd7eab59d9f5025a408d16`
- DEV-003 execution archive: `2fa7ef17e3b9efaf891a77c63797e18ad09e1fa3`
- Sol REP-001 zero-model protocol freeze: `5c8dc1fab267baaf61b0175cb8103cb3ac7bea7f`
- Sol REP-001 pre-execution handoff refresh: `3d930d2f448e8ed1c53c928a9fd61417f130d6f3`
- Sol REP-001 execution archive: `c1c933d654b66176751725a83aac7368d14f5ebe`
- Ordinal-12 diagnosis handoff refresh: `7172a54`
- Sol REP-002 zero-model protocol freeze: this commit
- Long-term route authority: `experiments/eve/README.md`
- Current gate authority: `experiments/eve/READINESS.md`
- Copy-paste next-session prompt: `experiments/eve/NEXT_SESSION_PROMPT.md`

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
- Historical Stage 4, Stage 5A DEV-001, DEV-002, completed DEV-003, and executed
  Sol REP-001 inputs and runtime evidence are immutable. Do not repair, retry,
  resume, import, rewrite, or clean them.

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

Protocol `EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-003`, version
`3.0.0`, SHA-256
`4c407b3e654d4e38f6f35b48e924863b5a9ef72c1e6b9569996e86f00105ad49`
has completed all 12 cells and 36 Luna sessions under ChatGPT subscription
authentication. The frozen protocol file still correctly retains its immutable
launch-input status `FROZEN_NOT_YET_EXECUTED`; actual execution is recorded in
`stage5a_review/dev003-execution-audit.json`.

The matrix used the canonical fork's clean Lean commit
`b490317186ef435670c2eeb16050a214cdbf9fe5`, fresh DEV-003 roots and ledger,
exact `/usr/bin/python3` 3.9.6 checkers, and no DEV-002 state. All 12 ledger rows
are completed with exit code zero. There was no retry, resume, or import.

Raw candidate passes are:

| Route | static | fixed | evolved |
|---|---:|---:|---:|
| direct | 0/6 | 0/6 | 0/6 |
| transport | 0/6 | 2/6 | 0/6 |

The four evolved cells produced and admitted nine failure-derived guidance
candidates. Ordinals 3, 6, and 9 each selected one exact candidate in a strictly
later iteration, so three cells are
`GUIDANCE_PRODUCED_AND_SELECTED_LATER`. Ordinal 12 produced and admitted three
candidates but selected none later, so it is `PRODUCED_NOT_SELECTED_LATER`.
Every rollout retained mandatory checker evidence; the DEV-002 empty-evidence
defect did not recur.

Four inter-cell preflights failed closed after detecting formal-state snapshot
drift: one `--execute` invocation and three zero-model `--check` invocations.
All four stopped before attempt reservation and model access. After state
quiescence and a passing zero-model check, the next frozen cell ran once. This
did not create a retry or duplicate cell, but a successor or Sol protocol must
repair the snapshot/quiescence handling for mutable SQLite sidecars. Sol
REP-001 is that separate repaired successor; it does not alter DEV-003 history.

## Current Stage 5B Sol REP-001 state

Protocol `EVE-STAGE5B-SOL-ENTRY-GAME-GUIDANCE-LIVENESS-REP-001`, version
`1.0.0`, SHA-256
`f532789fc76d282a386c6719bd16fd9da75ea05904d16035df06bfbde52e4a2f`
has consumed all 12 unique cells and 36 `gpt-5.6-sol` solver sessions under
explicit user authorization and ChatGPT subscription authentication. The frozen
protocol file correctly retains its immutable launch-input status
`FROZEN_NOT_YET_EXECUTED`; actual execution is recorded separately in
`stage5b_review/sol-rep001-execution-audit.json`.

The replication preserves DEV-003's two tasks, cases, 12-cell order, seeds,
condition semantics, three iterations, one worker, exact prompt/guidance/checker
bytes, evaluator, pinned EvE and Lean sources, eight-turn budget, 900-second
timeout, and `low` reasoning effort. The model identity alone changes from
`gpt-5.6-luna` to `gpt-5.6-sol`; protocol-owned paths, RNG domain, 12 run roots,
and ledger are fresh. No historical runtime state was imported, and there was
no retry, resume, or duplicate cell.

The raw candidate passes are direct static/fixed/evolved `4/6, 6/6, 6/6` and
transport `4/6, 4/6, 2/6`, or 26/36 total. The first 11 cells have successful
machine audits: eight controls are `CONTROL_PASSED_NO_RETENTION`, while evolved
ordinals 3, 6, and 9 are `GUIDANCE_PRODUCED_AND_SELECTED_LATER`. Those three
audited cells establish three local failure-derived production, admission, and
strictly-later-selection chains. They do not establish a causal or
model-capability conclusion.

Ordinal 12 completed its three model sessions and the underlying EvE process
returned zero, but its first Phase 2 optimizer task failed closed because the
final checker event did not match the final candidate. Phase 2 skipped that
task, leaving iteration-1 `solver_rollout_completed` telemetry absent. The
mandatory post-run audit therefore exits 2 with `solver rollout telemetry is
incomplete`. Its raw scores `0, 1, 1` and one iteration-2 produced/admitted but
not-later-selected guidance candidate are preserved, but the cell has no final
machine-audit classification. Sol REP-001 is consequently an executed matrix
with an incomplete post-run audit, not a clean whole-matrix replication or a
complete Sol-versus-Luna comparison.

Two additional inter-cell guards failed before reservation or model access:
one execute invocation before ordinal 3 did not reach logical quiescence, and
one zero-model check before ordinal 6 observed a projected-state change. After
a passing zero-model check, each cell executed once. These are not retries and
created no extra session, but they show the repaired snapshot contract did not
eliminate every settling event.

## Current Stage 5B Sol REP-002 state

Read-only diagnosis is frozen in
`stage5b_review/sol-rep001-ordinal12-diagnosis.json`. The last ordinal-12
iteration-1 checker event covered candidate SHA-256 `37db0198...`; at 15:33:26Z
the model used `apply_patch` to replace the two proof bodies, producing final
candidate `b19c421a...`, and made no subsequent checker call. The preserved
evaluator used those final bytes and Lean rejected the replacement proofs.
This deterministically explains the mismatch without a snapshot race.

The independent successor protocol is
`EVE-STAGE5B-SOL-ENTRY-GAME-GUIDANCE-LIVENESS-REP-002`, version `1.0.0`, SHA-256
`318557e77f6b2126b813e522eea15bce03cb792639b2f537e4d53893749f7a8f`.
It has fresh configs, overlays, RNG domain, root parent
`.runtime/stage5b-sol-rep002-runs`, and attempt ledger
`.runtime/stage5b-sol-rep002-attempt-ledger.sqlite3`; neither formal path exists.

The REP-002 wrapper invokes the exact immutable checker after `_run_agent`
returns and before `evaluate_workspace`, then revalidates candidate, checker,
and event chain after evaluation. Every rollout emits exactly one
`solver_rollout_terminal` event. Invalid evidence is explicitly
`RUN_FAILED_CHECK_EVIDENCE_CONTRACT`; the rejected task cannot reach evaluation,
finalization, or optimizer production. The auditor recognizes terminal
rejection directly rather than reporting generic incomplete telemetry.

Scientific inputs are unchanged from REP-001: model `gpt-5.6-sol`, low effort,
tasks, cases, seeds, conditions, matrix order, three iterations, one worker,
prompt/guidance/checker bytes, evaluator, pinned EvE/Lean source, eight turns,
900 seconds, and zero retry/resume/import. Preparation and validation made zero
model calls and consumed zero Sol quota. Execution is not authorized, and the
old REP-001 authorization does not transfer.

## Last verified evidence

- The Sol attempt ledger has 12 unique completed exit-zero rows, SHA-256
  `3b393f9085ad832da85c02eda8055b6c7ccf89783343348c30497b30befa32f1`.
- Eleven machine audits replay byte-identically. Ordinal 12 reproducibly fails
  closed with exit 2 and `solver rollout telemetry is incomplete`.
- All 25 Sol attempt/lineage databases pass SQLite integrity checking. No
  checkpoint, repair, or evidence write was performed during review.
- Token evidence contains exactly 36 top-level subscription sessions and
  attempt records: 206 agent turns, 6,924,408 input tokens, 5,800,192 cache-read
  tokens, and 125,536 output tokens. The adapter reports USD 0; that is not
  evidence of zero subscription quota use or remaining capacity.
- DEV-002 and DEV-003 ledger SHA-256 remain respectively
  `e593bf5726b20aa20f1cbb15882b7c2e9e169080233f346d67b48d6543a37922`
  and `3d0ab59f2022d6bdbb04774688e3ab2cd9981a2f31a6f34bd2b1772950f2d664`.
- Pre-execution validation remains historical: Sol targeted suite 16 passed;
  full EVE suite 103 passed with exactly the same two checkout-dependent skips;
  all 12 `--check`/`--dry-run` cells and the Stage 4, DEV-002, DEV-003, and Sol
  protocol verifiers passed.
- REP-002 validation: 19 targeted tests pass; the full EVE suite passes 122
  tests with the same two checkout-dependent skips; Stage 4 local evidence,
  DEV-002, DEV-003, REP-001, and REP-002 verifiers pass; all 12 REP-002 checks
  and all 12 dry-runs pass against the clean pinned Lean checkout.
- The post-check-mutation regression proves the wrapper appends a new event for
  the mutated candidate, and the rejection regression proves the auditor
  classifies `RUN_FAILED_CHECK_EVIDENCE_CONTRACT` instead of incomplete
  telemetry.
- The two full-suite skips are unchanged and individually recorded:
  `test_accepted_efg_fixture_compiles_in_isolated_solver_home` and
  `test_actual_hydra_loader_parses_both_configs_when_checkout_is_supplied`.
- DEV-003 detached protocol, frozen assets, committed Lean closure, dependency
  revisions, clean-checkout environment verification, and ledger order passed.
- All 12 completed DEV-003 launches satisfy the frozen identity, Luna/low model,
  3-iteration/1-worker compute, zero retry/resume/import, clean preflight, and
  no-DEV-002-state assertions.
- Ledger and all 24 solver/optimizer lineage databases pass integrity checks.
  Re-running the DEV-003 auditor for every root reproduced all 12 machine reports
  byte-identically.
- DEV-003 token evidence contains 36 top-level subscription sessions, 150 agent
  turns, 11,573,732 input tokens, 10,075,648 cache-read tokens, and 200,096
  output tokens. The adapter reports USD 0, which does not mean the sessions
  consumed no subscription quota.
- DEV-002 state reuse or mutation is zero; its ledger SHA-256 remains
  `e593bf5726b20aa20f1cbb15882b7c2e9e169080233f346d67b48d6543a37922`.

These facts establish three audited local guidance-liveness mechanism
observations in the Sol execution. The ordinal-12 evidence gap, answer-visible
`n=2` matrix, uncontrolled provider sampling, non-independent review, and
pre-reservation guard anomalies establish no clean cross-model replication,
causal EvE effect, model capability, benchmark readiness, or evaluation
completion.

## Next bounded action and stop condition

Stop at the frozen, zero-model-validated REP-002 protocol. All REP-001 attempt
slots remain consumed and immutable; do not retry, resume, import, repair in
place, or reuse their runtime state. Do not call REP-002 `--execute`, start a
model, consume quota, or create its formal root/ledger without a new explicit
user authorization naming REP-002 and acknowledging model/quota use.

The next bounded action is independent read-only review of REP-002 or a user
decision at that authorization gate. If execution is authorized, reverify the
exact protocol SHA, clean checkouts, absent REP-002 formal state, frozen matrix
order, authentication, and quota acknowledgement before reserving ordinal 1.

## Session cleanup and repository state

- On 2026-08-23, the disposable directory
  `/private/tmp/sol-rep001-reaudit.CI8N6u` was removed. It contained only 11
  reproducible audit-output copies; no formal run evidence was removed.
- `experiments/eve/.runtime`, the clean Lean checkout, and every historical
  Stage 4/5A/5B root and ledger remain preserved.
- At handoff generation, the remote branch contains diagnosis handoff
  `7172a54`; the REP-002 freeze is the current task-owned update pending its
  final commit/push. The mixed non-EVE worktree remains user-owned and untouched.

## Local versus GitHub evidence

GitHub stores the tracked protocols, code, reviews, documentation, and commit
history. Runtime evidence under `experiments/eve/.runtime/` is ignored and
remains only on this machine. A fresh clone cannot reconstruct historical
Stage 4/DEV-002/DEV-003/Sol transcripts, but their tracked audit hashes remain
authoritative summaries. Sol REP-001 runtime evidence now exists only on this
machine and must be preserved. REP-002 has no runtime evidence because it has
not executed. Both protocols' Lean environments are tied to a clean committed
source tree rather than the user's uncommitted Lean work.

## Bootstrap prompt for the next conversation

Use the authoritative copy-paste prompt in
[`NEXT_SESSION_PROMPT.md`](NEXT_SESSION_PROMPT.md). It includes the repository
checkpoint, immutable history, DEV-003 and Sol results, ordinal-12 evidence gap,
quota accounting, claim boundary, validation expectations, and the stop before
any successor model call. Keep that standalone prompt synchronized whenever
this handoff changes.
