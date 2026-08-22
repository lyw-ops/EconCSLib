# EVE next-session handoff prompt

Last updated: 2026-08-23

Copy the text below into the next Codex task. This prompt transfers repository
state and safety boundaries. It does not authorize any historical retry or a
new model call/execution under a successor identity.

```text
Open /Users/lyuyuwei/Documents/EconCSlib and continue on branch
experiment/eve-stage5a. Start by checking facts rather than assuming this
handoff is still current.

Read and follow the root AGENTS.md and experiments/eve/AGENTS.md in full. Then
read, in order:

- experiments/eve/HANDOFF.md
- experiments/eve/README.md
- experiments/eve/READINESS.md
- experiments/eve/stage5a_review/dev002-execution-audit.json
- experiments/eve/stage5a_review/dev003-audit.json
- experiments/eve/stage5a_review/dev003-execution-audit.json
- experiments/eve/stage5b_sol_rep001_protocol.json
- experiments/eve/stage5b_review/sol-rep001-audit.json
- experiments/eve/stage5b_review/sol-rep001-execution-audit.json
- experiments/eve/stage5b_review/sol-rep001-ordinal12-diagnosis.json
- experiments/eve/stage5b_sol_rep002_protocol.json
- experiments/eve/stage5b_review/sol-rep002-audit.json

Inspect git status --short --branch, recent commits, every remote, the upstream
tracking relationship, and the exact target files before changing anything.
The canonical handoff repository is https://github.com/lyw-ops/EconCSLib, and
the branch must track fork/experiment/eve-stage5a. The expected DEV-003
execution-archive commit is
2fa7ef17e3b9efaf891a77c63797e18ad09e1fa3. The expected Sol REP-001
zero-model protocol-freeze commit is
5c8dc1fab267baaf61b0175cb8103cb3ac7bea7f. The expected Sol REP-001 execution
archive commit is c1c933d654b66176751725a83aac7368d14f5ebe. The live local
branch must also contain ordinal-12 diagnosis handoff 7172a54 and the later
REP-002 zero-model freeze commit recorded in HANDOFF.md. Verify the live HEAD,
upstream, and remote rather than trusting these expected values.

The worktree contains extensive user-owned changes outside experiments/eve/.
Preserve all of them. Never restore, format, stage, commit, or otherwise absorb
unrelated files. Stage only files genuinely owned by the current EVE task, and
review the staged diff before committing.

Immutable historical facts:

1. Stage 4 protocol EVE-STAGE4-LUNA-ENTRY-GAME-DEV-002 completed 12 cells and
   24 Luna sessions. No evolved rollout produced an optimizer candidate, so it
   did not demonstrate guidance evolution.
2. Stage 5A DEV-001 was invalidated before execution with zero run roots and
   zero model sessions. Preserve its evidence.
3. Stage 5A DEV-002 is
   EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-002 v2.0.0, SHA-256
   6dafcb0d2476cd2f21df0c976f4f380488f1dcec067d7a0e7ba0802631045a05.
   It completed 12 cells and 36 Luna sessions, but its Python-3.9-incompatible
   datetime.UTC checker and empty-list-permitting auditor made it permanently
   executed-defective. Do not retry, resume, import, repair, or reclassify it.
4. Stage 5A DEV-003 is
   EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-003 v3.0.0, SHA-256
   4c407b3e654d4e38f6f35b48e924863b5a9ef72c1e6b9569996e86f00105ad49.
   Its frozen protocol file correctly retains the immutable launch-input field
   FROZEN_NOT_YET_EXECUTED; never rewrite that field after execution.
5. DEV-003 used ChatGPT subscription authentication, the clean canonical Lean
   source commit b490317186ef435670c2eeb16050a214cdbf9fe5, exact /usr/bin/python3
   3.9.6 checkers, fresh DEV-003 roots/ledger, and no DEV-002 state. It completed
   12/12 cells and 36/36 Luna sessions once, in frozen order, with all ledger
   rows exit code 0 and no retry/resume/import.
6. All 36 DEV-003 rollouts retained mandatory checker evidence. All 12 machine
   audits replay byte-identically. Raw candidate passes are direct static 0/6,
   fixed 0/6, evolved 0/6; transport static 0/6, fixed 2/6, evolved 0/6.
7. The four evolved DEV-003 cells produced and admitted nine failure-derived
   guidance candidates. Ordinals 3, 6, and 9 each selected one exact candidate
   in a strictly later iteration. Ordinal 12 produced and admitted three but
   selected none later. This gives three clean local liveness-mechanism chains.
8. Four inter-cell preflights failed closed on formal-state snapshot drift:
   one execute invocation and three zero-model checks. Each stopped before
   attempt reservation and model access, so it consumed no cell or session and
   caused no retry. The observed trigger involved mutable SQLite sidecar state
   settling or being opened. Sol REP-001 introduced a logical-snapshot repair
   under a separate identity; never backport it into DEV-003 or rewrite its
   historical evidence.
9. experiments/eve/.runtime is Git-ignored and local to this machine. Preserve
   all Stage 4, DEV-001, DEV-002, DEV-003, and Sol REP-001 runtime evidence. A
   fresh GitHub clone cannot reconstruct local transcripts merely from tracked
   summaries.
10. Stage 5B Sol REP-001 is
    EVE-STAGE5B-SOL-ENTRY-GAME-GUIDANCE-LIVENESS-REP-001 v1.0.0, SHA-256
    f532789fc76d282a386c6719bd16fd9da75ea05904d16035df06bfbde52e4a2f.
    Its immutable protocol file correctly remains FROZEN_NOT_YET_EXECUTED as a
    launch-input fact. The separate execution record shows that all 12 cells and
    36 Sol solver sessions were then consumed once under explicit authorization.
11. Sol REP-001 exactly preserves DEV-003's tasks, cases, conditions, seeds,
    matrix order, compute, prompt/guidance/checker bytes, evaluator, pinned EvE
    and Lean sources, turn budget, timeout, and low reasoning effort. Only the
    model identity changes to gpt-5.6-sol; protocol paths, RNG domain, root, and
    ledger are fresh and no historical runtime state was reused. There was no
    retry, resume, import, or duplicate cell.
12. Its durable-files-and-sqlite-logical-content-v1 snapshot contract ignores
    directory mtimes, SQLite page layout, WAL/SHM/journal sidecars, and
    checkpoint transitions while detecting ordinary-file and committed SQLite
    changes. Three identical samples are required before and after preflight.
    Even after this repair, one execute invocation before ordinal 3 and one
    zero-model check before ordinal 6 failed closed before reservation/model
    access. They consumed no attempt or session and caused no retry.
13. Raw Sol candidate passes are direct static/fixed/evolved 4/6, 6/6, 6/6 and
    transport 4/6, 4/6, 2/6. The first 11 machine audits replay
    byte-identically: eight controls have no retention, and evolved ordinals 3,
    6, and 9 each establish one failure-derived produced/admitted/later-selected
    guidance chain.
14. Ordinal 12 completed all three sessions with raw scores 0, 1, 1. Its first
    Phase 2 optimizer task was skipped because the final checker event did not
    match the final candidate, so iteration-1 solver_rollout_completed telemetry
    is absent. The mandatory post-run auditor reproducibly exits 2 with solver
    rollout telemetry is incomplete. One iteration-2 guidance candidate is
    locally produced/admitted but not selected later; the whole cell remains
    unclassified by the mandatory audit.
15. Token accounting uses exactly 36 top-level token_usage.json records: 206
    agent turns, 6,924,408 input tokens, 5,800,192 cache-read tokens, and 125,536
    output tokens. The ChatGPT subscription adapter reports USD 0; this neither
    means zero quota consumption nor exposes remaining quota.
16. The Sol ledger has 12 unique completed underlying-EvE exit-zero rows; all
    attempt slots are consumed. Eleven audits pass byte-identically, ordinal 12
    fails closed as above, and all 25 attempt/lineage databases pass integrity
    checking. The execution is not a clean whole-matrix replication.
17. Pre-execution validation remains historical: Sol targeted tests passed
    16/16; the full EVE suite passed 103 tests with the same two
    checkout-dependent skips; all 12 Sol cells passed zero-model --check and
    --dry-run before execution.
18. Read-only ordinal-12 diagnosis is tracked in
    stage5b_review/sol-rep001-ordinal12-diagnosis.json. The last checker event
    covered candidate 37db01983134fada694c78a91d4752826de09de094e961a5ade7bb01f0e546a4;
    the model then applied a patch producing final/evaluated candidate
    b19c421a71f049a078413e7fcdb8e06a1ad934c9d39fd0f7daec2f4eb30ca9e6
    and made no later checker call. This is deterministic post-check mutation,
    not a snapshot race.
19. The separate successor is
    EVE-STAGE5B-SOL-ENTRY-GAME-GUIDANCE-LIVENESS-REP-002 v1.0.0, SHA-256
    318557e77f6b2126b813e522eea15bce03cb792639b2f537e4d53893749f7a8f.
    It uses fresh configs, overlays, RNG domain, run-root parent, and attempt
    ledger. Neither formal REP-002 root nor ledger exists.
20. REP-002 preserves REP-001's model, effort, scientific inputs, matrix,
    prompts, initial guidance, checker, evaluator, pinned sources, compute,
    turn/timeout, and no-retry policy. Its wrapper alone adds an immutable
    checker call after _run_agent and before evaluate_workspace, followed by
    post-evaluation snapshot revalidation and exactly one terminal event per
    rollout. Invalid evidence is RUN_FAILED_CHECK_EVIDENCE_CONTRACT and cannot
    produce an optimizer.
21. REP-002 pre-execution validation passed 19 targeted tests, 122 full-suite
    tests with the same two checkout-dependent skips, all historical and new
    protocol verifiers, all 12 zero-model checks, and all 12 dry-runs. It made
    zero model calls, consumed zero quota, and wrote zero formal state.

Claim boundary:

- DEV-003 establishes valid public-development raw outcomes, clean mandatory
  checker evidence, and three local production/admission/later-selection
  mechanism observations.
- It does not establish a causal EvE effect, model capability, benchmark
  readiness, evaluation completion, independent human review, or a Sol result.
- Sol REP-001 establishes 12 consumed attempts, exact quota accounting, raw
  public-development outcomes, 11 fully audited cells, and three local liveness
  chains. The ordinal-12 evidence gap prevents a clean whole-matrix replication
  or complete Sol-versus-Luna comparison.
- Provider model sampling remains uncontrolled, and the answer-visible matrix
  has only n=2 seeds per condition.
- REP-002 establishes only a reviewed protocol repair and zero-model gate
  success. It has no result and no inherited execution authorization.

Start in read-only review mode. All DEV-003 and Sol REP-001 attempts are
consumed: do not retry, resume, import, repair in place, or invoke either old
--execute path. REP-002 is frozen and zero-model validated but unexecuted. Do
not invoke its --execute path, start a model, consume quota, or create its
formal root/ledger unless the user gives new explicit authorization naming
REP-002 and acknowledging model/quota use. Historical authorization never
transfers to a successor.

The next bounded action is independent read-only REP-002 review or a user
decision at that authorization gate. Before any separately authorized
execution, verify the exact protocol SHA, clean EvE and Lean checkouts, absent
REP-002 formal state, frozen ordinal-1 matrix selection, authentication, and
quota acknowledgement. Never modify or reuse REP-001 runtime evidence.

For any task, run validation proportionate to the changed files. For EVE
protocol work, at minimum run the full experiments/eve test suite, relevant
targeted tests, Stage 4 local-evidence verification/no-recheck audit, DEV-002
and DEV-003 historical protocol verifiers, the Sol REP-001 and REP-002
clean-checkout verifiers, detached hashes/environment checks,
all planned zero-model checks/dry-runs when relevant, and git diff --check.
Record every skip individually. Never claim natural-language statements are
machine verification.

After completing an authorized task, update experiments/eve/HANDOFF.md and this
prompt if the handoff state changed. Commit only task-owned tracked files, push
to fork/experiment/eve-stage5a as required by the handoff policy, and verify the
exact remote commit. Then stop at the next explicit authorization boundary.
```
