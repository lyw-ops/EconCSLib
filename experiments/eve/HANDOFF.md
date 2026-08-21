# EVE concise handoff

Last updated: 2026-08-21

## Repository checkpoint

- Local repository: `/Users/lyuyuwei/Documents/EconCSlib`
- Fork: <https://github.com/lyw-ops/EconCSLib>
- Experimental branch: `experiment/eve-stage5a`
- Published WIP checkpoint: `07a48d3` (`WIP: prepare Stage 5A guidance liveness protocol`)
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

The WIP branch contains protocol
`EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-001`, prompts, configs,
lineage observer/auditor, tests, README/READINESS updates, and a protocol review
record. No Stage 5A run root, EvE execution, Luna session, new guidance, or Sol
replication exists.

The current 001 protocol is **not authorized for execution**. A Codex review
found four blocking defects:

1. The frozen artifact set does not freeze the transitive EconCSLib Lean import
   closure. Several imported EFG modules are currently modified in the mixed
   worktree, while the protocol verifier can still pass.
2. `run_stage5a.py` creates a new timestamped root on every invocation but does
   not enforce one attempt per cell or the frozen matrix order.
3. The liveness audit observes a failure and a guidance change in the same
   rollout but cannot prove that the guidance change happened after the real
   Lean failure.
4. Both route prompts say to work only in `solver/Candidate.lean` and later
   require writing `guidance/docs/learned.md`, creating an edit-boundary
   contradiction that can suppress guidance production.

Do not silently repair and continue using 001 as though it had always been
valid. Preserve the WIP checkpoint, record the pre-execution invalidation or
supersession, and prepare a new protocol ID/version (normally DEV-002) with new
hashes and review evidence.

## Last verified evidence

Before this handoff was created:

- 69 EVE tests passed; 2 environment-dependent tests were skipped as designed.
- Stage 4 machine audit and review verification passed with local evidence.
- The existing Stage 5A detached protocol hash verified.
- All 12 planned Stage 5A `--check` calls passed.
- All 12 planned Stage 5A `--dry-run` calls passed.
- The checks made zero Stage 5A model calls and wrote no Stage 5A run root.

These successes establish implementation loading and safe preflight only. They
do not override the four protocol blockers above.

## Next bounded task

Repair the four blockers without touching unrelated worktree changes:

1. choose a reproducible clean Git tree or freeze and verify the complete Lean
   dependency closure and build metadata;
2. add a durable pre-launch attempt/order ledger that fails before model access;
3. record protected event ordering and guidance hashes at each genuine Lean
   check so failure-derived changes are auditable;
4. make the Candidate and guidance edit surfaces explicit and non-contradictory;
5. add negative regression tests for every repair;
6. invalidate/supersede 001, freeze the new protocol and hashes, update review,
   README, READINESS, and this handoff;
7. rerun the full EVE suite and all 12 safe checks/dry-runs.

Stop after review and freeze. Do not execute Luna until the user explicitly
authorizes the new protocol.

## Local versus GitHub evidence

GitHub stores tracked code, documentation, and commit history. Runtime evidence
under `experiments/eve/.runtime/` is ignored and remains only on this machine.
A fresh clone or cloud task must not claim that the missing runtime directory
means the historical runs did not occur; use tracked audit hashes and request
the local evidence when full re-verification is required.
