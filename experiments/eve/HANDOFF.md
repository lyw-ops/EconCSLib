# EVE concise handoff

Last updated: 2026-08-21

## Repository checkpoint

- Local repository: `/Users/lyuyuwei/Documents/EconCSlib`
- Fork: <https://github.com/lyw-ops/EconCSLib>
- Experimental branch: `experiment/eve-stage5a`
- Handoff-policy checkpoint: `1258e05` (`docs(eve): define handoff repository policy`)
- DEV-001 WIP checkpoint: `07a48d3` (`WIP: prepare Stage 5A guidance liveness protocol`)
- Long-term route authority: `experiments/eve/README.md`
- Current gate authority: `experiments/eve/READINESS.md`

Always verify the live branch, HEAD, upstream, and worktree instead of assuming
the checkpoint above is still current.

## Handoff repository policy

- Treat <https://github.com/lyw-ops/EconCSLib> as the canonical handoff
  repository for this work.
- At the end of every completed task, update this handoff document with the
  completed scope, validation results, execution status, remaining blockers,
  and next bounded task.
- Commit and push every completed task's in-scope tracked changes to the
  current experimental branch on that repository; completed tracked work must
  not remain local-only.
- Stage only files owned by the completed task. Never mix unrelated or
  user-owned worktree changes into a handoff commit.
- Before declaring handoff complete, verify the pushed branch and commit and
  confirm that every tracked input needed to reproduce the result is present
  in the handoff repository. Ignored runtime evidence remains governed by the
  local-evidence policy below.

## Research direction

EVE studies generated Lean proofs for algorithmic game theory with deterministic
filtering and Codex AI review. The central mathematical design has two routes:

1. **Direct route:** prove the exercise using concrete objects close to the
   statement.
2. **Transport route:** encode the exercise into the abstract objects used by
   an existing general theorem, build a `RefinementCertificate` proving that
   exercise assumptions establish theorem assumptions, instantiate the theorem,
   and transport its conclusion back to the exact concrete exercise statement.

Ordinary tasks may use either route. Paired experiments keep the two solver
workspaces independent and compare them only through deterministic evaluation.

Model order remains Luna for low-cost engineering and liveness development,
then Sol for an equal-condition full replication only after the protocol is
valid and the Luna gate has closed.

## Completed stages

- Stage 0: EvE sidecar scaffold and local deterministic smoke infrastructure.
- Stage 1: local deployment and bounded Luna manual smoke; smoke 002 scored
  `1.0` after the isolated Lean toolchain repair.
- Stage 2: Entry Game direct/transport pair, accepted fixtures, agreement
  evaluator, and 12 rejected mutations.
- Stage 3: public review micro-benchmark with Codex AI review; no mutation false
  accept and no claim of independent human review.
- Stage 4: protocol `EVE-STAGE4-LUNA-ENTRY-GAME-DEV-002`; all 12 cells and 24
  Luna sessions completed once and were machine re-audited. Direct run success
  was static `1/2`, fixed `2/2`, evolved `2/2`; transport was static `1/2`,
  fixed `0/2`, evolved `0/2`. All evolved rollouts produced zero optimizer
  candidates, so Stage 4 does not demonstrate guidance evolution.

Stage 4 tracked records and local `.runtime` evidence are historical and must
not be rewritten or deleted.

## Current Stage 5A state

Protocol `EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-001` is invalidated
in full before execution. The WIP checkpoint, detached hash, original Codex AI
review, and four blockers are preserved; it created zero Stage 5A run roots and
started zero model sessions.

The executed protocol is
`EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-002`, version `2.0.0`, hash
`6dafcb0d2476cd2f21df0c976f4f380488f1dcec067d7a0e7ba0802631045a05`.
Its immutable launch status remains `FROZEN_NOT_YET_EXECUTED`; do not rewrite
that frozen historical input after execution. The pre-execution review is
`stage5a_review/dev002-audit.json`, and the tracked post-execution record is
`stage5a_review/dev002-execution-audit.json`.

All 12 cells and 36 Luna sessions completed once in frozen order with fresh run
roots, zero retry/resume/import, and ledger exit code zero. The 12 machine
audits reproduced byte-identically. Raw candidate passes were direct static
`0/6`, fixed `0/6`, evolved `0/6`; transport static `3/6`, fixed `2/6`, evolved
`1/6`. Four failure-derived guidance candidates were produced and admitted.
One candidate from direct/2718/evolved iteration 1 was selected in iterations 2
and 3, giving one valid local `GUIDANCE_PRODUCED_AND_SELECTED_LATER` chain.

Post-run review found a blocking frozen-checker defect. The isolated solver used
Python 3.9.6, while both immutable checkers record timestamps through
`datetime.UTC`, which is unavailable before Python 3.11. All 36 sessions hit the
defect at least once (91 failed invocations). Runtime workarounds yielded 57
valid recorded events in 11 sessions, but 25 rollouts retained an empty check
list. The existing auditor permits an empty list, so its pass does not establish
the full per-edit feedback contract. Preserve DEV-002 as executed historical
evidence: do not retry it or silently repair its frozen artifacts. The ordinal-6
chain is a genuine local mechanism observation, but the whole matrix is not a
clean protocol execution and does not authorize Sol replication.

## Last verified evidence

At this handoff:

- The frozen Lean entry target built successfully (`3096` jobs).
- 75 EVE tests passed; 2 environment-dependent tests were skipped as designed.
- The DEV-002 detached protocol hash and all frozen inputs verified.
- All 12 planned Stage 5A `--check` calls passed.
- Preflight wrote no DEV-002 run root or ledger and made zero model calls.
- All 12 execution attempts completed with exit code zero and consumed exactly
  36 Luna sessions; no retry, resume, or import occurred.
- The ledger contains exactly the frozen 12-cell order, and all 12 post-run
  audits reproduced byte-identically.
- Post-run transcript review found the checker-runtime defect above in all 36
  sessions; 25/36 rollouts have no recorded check event.

These records establish raw public-development execution and one local liveness
chain only. They do not establish a clean comparison, causal EvE effect, model
capability, benchmark readiness, evaluation completion, or Sol readiness.

## Next bounded task

Stop after recording the executed DEV-002 defect. Preserve all Stage 4 and
Stage 5A runtime evidence and unrelated worktree changes. The next bounded task
is review-only preparation of a new protocol identity, normally DEV-003: use a
Python-3.9-compatible UTC expression, execute the immutable checker with the
exact solver runtime during preflight, make missing required check evidence fail
closed, add regressions, use fresh roots and a fresh ledger, and obtain a new
review. Do not execute DEV-003 or start Sol without separate user authorization.

## Local versus GitHub evidence

GitHub stores tracked code, documentation, and commit history. Runtime evidence
under `experiments/eve/.runtime/` is ignored and remains only on this machine.
A fresh clone or cloud task must not claim that the missing runtime directory
means the historical runs did not occur; use tracked audit hashes and request
the local evidence when full re-verification is required. The DEV-002 execution
hashes, raw outcomes, liveness events, and checker defect are tracked in
`stage5a_review/dev002-execution-audit.json`.

The current mixed worktree also contains 47 locally modified Lean files whose
hashes are frozen by `stage5a_lean_environment.json` but whose changes are not
owned by the EVE handoff task. They must not be staged without separate
authorization. Consequently, the EVE protocol and execution audit can be pushed
independently, but a fresh clone of the handoff repository cannot yet reproduce
the frozen local Lean environment. Resolve that scope explicitly or prepare a
successor protocol against a clean committed Lean tree before claiming a
repository-complete handoff.
