# EVE next-session handoff prompt

Last updated: 2026-08-22

Copy the text below into the next Codex task. This prompt transfers repository
state and safety boundaries. It does not authorize a model call, a DEV-003
retry, or Sol replication.

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

Inspect git status --short --branch, recent commits, every remote, the upstream
tracking relationship, and the exact target files before changing anything.
The canonical handoff repository is https://github.com/lyw-ops/EconCSLib, and
the branch must track fork/experiment/eve-stage5a. The expected DEV-003
execution-archive commit is
2fa7ef17e3b9efaf891a77c63797e18ad09e1fa3; verify the live local and remote
state instead of trusting the expected value.

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
   settling or being opened. Any successor must fix snapshot/quiescence handling
   under a new protocol identity and add regression coverage.
9. experiments/eve/.runtime is Git-ignored and local to this machine. Preserve
   all Stage 4, DEV-001, DEV-002, and DEV-003 runtime evidence. A fresh GitHub
   clone cannot reconstruct local transcripts merely from tracked summaries.

Claim boundary:

- DEV-003 establishes valid public-development raw outcomes, clean mandatory
  checker evidence, and three local production/admission/later-selection
  mechanism observations.
- It does not establish a causal EvE effect, model capability, benchmark
  readiness, evaluation completion, independent human review, or a Sol result.
- Provider model sampling remains uncontrolled, and the answer-visible matrix
  has only n=2 seeds per condition.

Start in read-only review mode. All DEV-003 attempts are consumed: do not retry,
resume, import, or execute DEV-003. Do not start Sol, make a Sol model call, or
consume quota. No separate Sol protocol is currently frozen or authorized.

If the user later asks only to prepare Sol replication, treat that as
review-only/zero-model protocol engineering unless they separately and
explicitly authorize execution. Use a new protocol ID/version, fresh roots and
ledger, a clean committed Lean boundary, and a repaired inter-cell
snapshot/quiescence contract. Do not reuse DEV-002 or DEV-003 runtime,
population, guidance, candidates, sessions, or attempt state. Preparation must
end at a frozen-not-executed state with detached hashes, regression tests,
fresh-clone verification, all planned check/dry-run calls, and a new review
record. A prepared protocol never implies execution authority.

For any task, run validation proportionate to the changed files. For EVE
protocol work, at minimum run the full experiments/eve test suite, relevant
targeted tests, Stage 4 local-evidence verification/no-recheck audit, DEV-002
and DEV-003 protocol verifiers, detached hashes/environment checks, and git
diff --check. Record every skip individually. Never claim natural-language
statements are machine verification.

After completing an authorized task, update experiments/eve/HANDOFF.md and this
prompt if the handoff state changed. Commit only task-owned tracked files, push
to fork/experiment/eve-stage5a as required by the handoff policy, and verify the
exact remote commit. Then stop at the next explicit authorization boundary.
```
