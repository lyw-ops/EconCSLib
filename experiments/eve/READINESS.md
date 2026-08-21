# EvE experiment readiness

- **Current status:** `STAGE5A_DEV003_FROZEN_REVIEW_READY_NOT_EXECUTED`;
  Stage 1 smoke 002 is closed at score one, Stage 2 direct/transport/pair and
  12 mutations are closed, Stage 3 Codex review verifies at score one, and
  all 12 Stage 4 Luna development cells completed and passed machine re-audit;
  Stage 5A DEV-001 is invalidated before execution, while all 12 DEV-002 cells
  and 36 Luna sessions executed once before post-run review found a blocking
  Python-3.9 checker defect; the separate DEV-003 identity closes those
  protocol-engineering defects and is frozen after zero-model validation
- **Not valid statuses:** `benchmark-ready`, `evaluation-complete`,
  `internal-pilot-complete`, or any model-capability conclusion
- **Formal pilot default:** disabled and not configured
- **Paid/long EvE execution:** the 12-cell public Stage 4 and defective DEV-002
  Stage 5A matrices are complete; DEV-003 has not executed; no benchmark,
  private evaluation, formal run, or Sol replication has occurred
- **EvE runner / `--execute`:** 26 executions: two Stage 1 smokes, 12 fresh
  Stage 4 cells, and 12 fresh Stage 5A cells; Stage 0 has not run
- **Luna sessions:** one read-only access smoke, two Stage 1 solver sessions,
  24 Stage 4 solver sessions, and 36 Stage 5A solver sessions

## What is ready

The official EvE `v0.2.0` tag and peeled commit are locked. The
external-checkout/config-overlay architecture keeps Python and EvE state out of
the Lean/Lake project. The existing public synthetic REPAIR seed and the new
public local EFG seed each have an exact single-file solver boundary,
deterministic higher-is-better scoring, equal worst evaluation/boundary scores,
offline check/dry-run paths, and positive/negative tests.

The external checkout at `/Users/lyuyuwei/Documents/eve-v0.2.0` matches the
official repository, annotated tag object, peeled commit, LICENSE, NOTICE,
`pyproject.toml`, `uv.lock`, and `.python-version`. `uv sync --locked`, the real
Hydra loader, the historical 45-test Stage 1 suite plus the current Stage 2--5A
extensions (latest full result: 87 tests run, 2 skipped), `--check`, `--dry-run`, the
launcher accepted fixture, and accepted-fixture compilation under an isolated
solver HOME pass. Twenty-six EvE executions and their bounded Luna sessions are
recorded below; the only other model call is the separately bounded access
smoke.

Codex project trust and all four EvE hook events are verified for that exact
checkout and hook payload. EvE's own trust helper reports no missing event;
26 upstream hook/isolation/sandbox tests pass, and sidecar `--check` reports the
trust state as available without exposing credentials. Trust confirmation ran
the session-start guard but submitted no ordinary prompt and made no model call.

On this macOS/Python 3.13 environment, uv's editable `.pth` receives a hidden
file flag that Python skips. The sidecar now sets `PYTHONPATH` to the
identity-verified checkout `src` for both dependency probe and execute while
retaining `uv --offline --frozen --no-sync`; upstream source and venv metadata
remain unchanged. Its dependency and hook probes now additionally use an
ephemeral writable `UV_CACHE_DIR`, and any future explicit execution uses a
per-run cache under its runtime root. This prevents a restricted outer sandbox
from turning a denied user-level uv cache read into a false unavailable result.

The EFG micro-pilot uses only `Interface.StructuralCore` and tests discovery of
the existing reachability/history bridge plus an occurrence-sensitive diamond.
Its accepted fixture passes; unfixed, compile failure, placeholder,
axiom/constant spoof, boundary violation, broad/additional import, wrong bridge
type, and missing-diamond fixtures all receive `score: 0.0`. This validates the
local evaluator and repaired Lean feedback path, not model capability.

Solver prompt `EVE-EFG-SOLVER-PROMPT-001` v1.0.0 is frozen, model-neutral, and
hash-anchored in `case.json`. It supplies explicit outcome, success criteria,
evidence limits, validation, and stop rules without embedding the accepted
proof. It was executed once by manual-smoke-001 and has status
`EXECUTED_SCORE_ZERO`; that status records a failed candidate, not a model
capability conclusion.

One user-provided manual candidate is archived under
`.runtime/manual-stage1-efg-reachability-001/` and receives deterministic
`score: 1.0` with every gate true after the protected seed was restored. Its
model attribution and Codex/EvE execution provenance are unverified, so it is
only proof/harness acceptance and not a Luna, EvE, benchmark, or capability
result.

Operator prompt `EVE-STAGE1-LUNA-PREFLIGHT-001` v1.0.0 is frozen and
hash-anchored in `operator_prompts/manifest.json`. It authorizes only local
preflight evidence collection and explicitly forbids `--execute`, `codex exec`,
model calls, network installation, and model-config migration. Its repaired
execution record is `READY_FOR_SEPARATE_MODEL_ACCESS_SMOKE`; the original
missing-checkout report is retained alongside it.

Operator prompt `EVE-STAGE1-LUNA-ACCESS-SMOKE-001` v1.0.0 remains frozen and
hash-anchored. Its first precondition pass was blocked by the outer sandbox's
denial of the user-level uv cache and is retained as
`access-smoke.blocked-outer-sandbox.json`; it attempted no model call. After
the sidecar diagnosis, the prompt's single authorized read-only, ephemeral
`gpt-5.6-luna` turn completed with status `LUNA_ACCESS_SMOKE_PASSED`, exact
message `EVE_LUNA_ACCESS_OK`, no tool event, and budget usage `1/1`. No retry,
fallback, Lean solver task, EvE execution, or config migration occurred.

Operator prompt `EVE-STAGE1-LUNA-CONFIG-MIGRATION-001` v1.0.0 is frozen and
hash-anchored. It wrote a new scoped Luna driver, selected it only for the EFG
micro-pilot, migrated the unrun manifest, and added structural coverage without
a model call. Initial validation exposed two stale protected hashes in
`case.json`; after explicit follow-up user authorization changed only those two
anchors, all then-current 42 tests and the complete non-model validation passed. Its report
is `LUNA_CONFIG_MIGRATION_READY`. The legacy Stage 0 driver remains unchanged,
and this report does not authorize a manual smoke.

Operator prompt `EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-001` v1.0.0 is frozen and
hash-anchored with status `EXECUTED_COMPLETED`. Its only authorized
`EvE-evolved-guidance` attempt completed one iteration and one Luna session in
5/10 turns, with zero resume/retry, deterministic score `0.0`, and no guidance
update. The candidate completed its first six declarations but failed the final
dependent equality theorem because `Sigma.ext_iff` supplied `HEq` where the
goal required `Eq`. This is completed pipeline evidence, not a solved candidate.

The post-run audit also found that the solver's isolated HOME could not discover
the already installed Lean 4.30.0 through `elan`, so its self-check attempted an
offline toolchain download and waited on a lock. The launcher now resolves and
version-checks the direct Lean/Lake binaries, prepends that toolchain directory
to the isolated solver PATH, and proves the accepted fixture compiles without
creating an isolated `.elan`. The repair and its regression tests made no model
or EvE call.

Operator prompt `EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-002` v1.0.0 is frozen and
hash-anchored with status `EXECUTED_COMPLETED`. Its fresh attempt used one Luna
session and 5/10 turns, resumed nothing, preserved the 001 run root, and passed
all 15 deterministic gates with score `1.0`. Independent re-execution of the
candidate and evaluator produced the same hashes, and the elan download/lock
failure did not recur. The audit was performed by Codex and is explicitly not
independent human review.

The Entry Game direct and transport accepted candidates each score `1.0`, their
pair agreement scores `1.0`, and all 12 mutation candidates are rejected at the
predeclared gates. The transport candidate constructs every refinement
certificate field and uses the fixed abstract theorems before returning the
conclusions to concrete profiles. Stage 3 records a complete Codex AI review
with no blocking finding on accepted candidates and no mutation false accept;
this is explicitly not independent human review.

Pinned-source and real-loader evidence now establish Stage 4 static, fixed,
and evolved semantics. A sidecar-only wrapper seeds the three `random.Random`
instances actually consumed by EvE sampling before the loop; upstream remains
unchanged. Codex/provider model sampling has no exposed seed, so only EvE
sampling is paired and end-to-end determinism is not claimed.

This is sufficient for Stage 0--4 public implementation and prompt-development
gates. Stage 4 itself does not close the EvE guidance-evolution effect gate: all
eight evolved rollouts left guidance unchanged and produced zero optimizer
candidates. Stage 5A later observed one local liveness chain but is not a clean
replication because of the checker defect recorded below. None of this
establishes that an agent can repair Mathlib or EFG code reliably, that EvE
improves an agent, that a model has a capability, that the minimal core should
change, or that the formal pilot is ready to evaluate.

Stage 5A DEV-001 is invalidated in full before execution: its artifact set did
not freeze transitive Lean dependencies, its timestamped roots did not enforce
attempt/order, its evidence did not prove failure-before-guidance-change, and
its edit instructions contradicted one another. The invalidation record anchors
the old protocol/review hashes and records zero run roots and zero model
sessions.

DEV-002 protocol preparation froze the pinned-source audit's exact Phase 2/Phase
3 order, the local-failure information boundary, the
minimum two iterations needed for production followed by selection, and the
provider RNG limitation. The frozen protocol uses three iterations, one worker,
8 turns, 900 seconds, no retry/resume/import, fresh roots under the dedicated
`stage5a-dev002-runs/` parent, and at most 36 Luna sessions across 12 cells. A
protocol-specific SQLite ledger reserves the exact next ordinal before model
access. The same route prompt bundle is byte-identical across all conditions;
fixed and evolved share initial guidance; static is empty; only evolved retains
changed guidance.

The Lean environment manifest freezes and re-verifies the complete 109-file
local import closure, Lake/toolchain metadata, and exact clean dependency
commits; the entry target builds before any reservation. The immutable checker
records a contiguous chain with checker, candidate, guidance-tree, exit, and
output hashes. Failure-derived classification requires a valid failing check
whose guidance snapshot differs from the final produced tree. Read-only audit
validates the complete ledger history and distinguishes changed, produced,
admitted, and selected-later events by exact ids/hashes. Static/fixed retention,
cross-run leakage, terminal-iteration no-opportunity, and provider-RNG
declarations fail closed. Both route prompts explicitly separate the candidate
and conditional guidance edit surfaces. Protocol hash verification and
`--check`/`--dry-run` are safe and make no model call, consume no quota, touch no
attempt ledger, and write no formal run result.

After explicit authorization, all 12 DEV-002 cells and 36 Luna sessions ran once
in order with fresh roots and zero retry/resume/import. All ledger rows are
completed with exit code zero, and all 12 machine-audit outputs reproduced
byte-identically. Four failure-derived guidance candidates were produced and
admitted. One direct/2718/evolved candidate produced in iteration 1 was selected
in iterations 2 and 3, yielding a valid local
`GUIDANCE_PRODUCED_AND_SELECTED_LATER` chain.

Post-run review nevertheless found a blocking checker defect. The exact solver
runtime was Python 3.9.6, but the frozen checker records timestamps with
`datetime.UTC`. All 36 sessions triggered the exception at least once, for 91
failed checker invocations. Runtime workarounds left 57 valid chained events in
11 sessions; 25 rollouts retained an empty check list. The auditor verifies a
nonempty chain when present but accepts an empty list, and the preflight did not
run the checker with the exact solver Python. DEV-002 is therefore an executed
but unclean protocol, not a clean liveness replication. Raw evaluator outcomes
and the ordinal-6 chain remain historical observations; they do not establish a
causal effect or model capability and do not authorize Sol. Review remains
Codex AI, not independent human review.

DEV-003 is now the review-ready, unexecuted successor protocol:
`EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-003` version `3.0.0`, hash
`4c407b3e654d4e38f6f35b48e924863b5a9ef72c1e6b9569996e86f00105ad49`.
It freezes new roots, ledger, order, RNG domain, config and overlay assets and
imports no DEV-002 runtime state. Both checker entrypoints are byte-identical
and Python-3.9-compatible. The wrapper and auditor require a nonempty valid
event chain, final-candidate match, exact Python/checker/command/output/exit
identity, and validated nonzero failures before failure-derived guidance can
count toward liveness.

The DEV-003 Lean environment is reproducible from the canonical committed tree
at `b490317186ef435670c2eeb16050a214cdbf9fe5`, not from the mixed operator
worktree. A separate fresh clone reproduced its 109-file closure, clean pinned
dependencies and entry build. All 12 `--check` calls ran a real deliberately
failing Lean candidate through exact `/usr/bin/python3` 3.9.6 in a disposable
workspace; all 12 dry-runs also passed. They made zero model calls, consumed
zero Luna quota, created no formal DEV-003 root or ledger, and did not inherit
or mutate DEV-002 state. DEV-003 remains `FROZEN_NOT_YET_EXECUTED` and needs
separate user authorization before `--execute`.

## Hard-disabled formal experiment boundary

The launcher allow-list contains exactly `mathlib-style-smoke`,
`efg-reachability-micro`, `entry-game-direct`, and `entry-game-transport`.
Stage 4 routes additionally require a frozen condition, one of the two frozen
EvE sampler seeds, and `--acknowledge-model-quota`. The launcher does not accept an
arbitrary config name, case directory, seed, evaluator, reference, gold, or
pilot path. It never reads `benchmarks/mathlib-style/heldout/private/`. There
is no formal/private Phase 4/5 application/evaluation config to enable accidentally. Any
request to run the 16-case formal pilot through this sidecar must hard-fail
until a separately reviewed implementation satisfies every gate below.

The dedicated `run_stage5a.py` accepts only the two Entry Game tasks, exact
protocol `EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-002`, conditions
`static|fixed|evolved`, and seeds `1729|2718`.
Unknown task, protocol, condition, or seed hard-fails. Its check/dry-run paths
never dispatch the execution function. All 12 DEV-002 attempt slots are now
consumed; the ledger rejects a rerun. Repair requires a new protocol identity,
fresh roots and ledger, new review, and separate execution authorization.

The successor `run_stage5a_dev003.py` accepts only the same frozen task,
condition, and seed matrix under the exact DEV-003 identity and additionally
requires a separate tracked-clean Lean checkout at the frozen source commit.
Its check path builds the frozen entry and runs safe preflight before formal
state; its dry-run path previews only. Neither dispatches execution. DEV-003
execution and Luna quota use are not currently authorized.

## Public Stage 4 Entry Game three-condition study

Stage 1a permits only this public synthetic/local task. It adds no declaration
under `EconCSLib/`, changes no carrier, leaves the exact StructuralCore closure
untouched, and does not update the Canonical/Frontend API-growth baseline. The
evaluator protects its facade/source/checker/config/seed/guidance assets before
Lean, requires the sole StructuralCore import and exact local declaration
types, checks empty target axiom output, then runs API-growth and governance.

`stage4_protocol.json` prepares `static`, `fixed`, and `evolved` for the Entry
Game direct and transport routes under shared model, effort, 6-turn limit,
timeout, tools, evaluator, two iterations, and one-attempt budget. Seeds `1729`
and `2718` control the three EvE sampler/worker-selection RNG streams and are
paired across conditions within each task. The adapter exposes no Codex model
seed or verbosity field, so provider sampling remains uncontrolled and no
end-to-end deterministic claim is permitted.

Pinned source hashes and real Hydra composition establish the three conditions:
static starts from an empty runtime guidance tree with optimizer production
disabled; fixed starts from the frozen route guidance with production disabled;
evolved starts from that same guidance with production enabled only for an
actually changed tree. Both Stage 4 task preflights report checkout identity,
locked environment, isolated Lean, authentication, and hook trust available.

All 12 protocol cells completed once in the frozen order with fresh run roots,
no resume/import/retry, and 24 solver sessions. `audit_stage4.py` independently
re-evaluated all 24 candidates and matched every archived status, score,
failure code, gate, and axiom record. Run-level outcomes are:

| Route | static | fixed | evolved |
|---|---:|---:|---:|
| direct | 1/2 | 2/2 | 2/2 |
| transport | 1/2 | 0/2 | 0/2 |

These are descriptive public-development outcomes at `n=2`; provider sampling
is unseeded. All evolved cells produced zero optimizer candidates, so no later
selection of evolved guidance occurred. Any resulting
carrier, StructuralCore, or public-API proposal must go through the EFG
freeze/governance human decision process; the micro-pilot cannot authorize it.

## Public Stage 5A guidance-liveness protocol

Protocol: `EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-002`, version
`2.0.0`. Its frozen file retains launch state `FROZEN_NOT_YET_EXECUTED`; that
historical input is not rewritten after execution. It supersedes only the
unexecuted, invalidated Stage 5A DEV-001 protocol. It relates to Stage 4 only as
a new development successor motivated by Stage 4's zero guidance changes and
does not supersede, modify, resume, import, or reclassify Stage 4 DEV-002
evidence.

The full matrix remains direct/transport × static/fixed/evolved × seeds
1729/2718 in frozen order. Each cell has three solver iterations and one
attempt. All 12 attempts and 36 Stage 5A model sessions are complete. If evolved
produces no candidate, report
`NO_GUIDANCE_PRODUCED`; if an admitted candidate is never sampled in a strictly
later iteration, report `PRODUCED_NOT_SELECTED_LATER`; if it is first produced
in iteration 3, report `PRODUCED_WITHOUT_LATER_OPPORTUNITY`. Production and
selection may never be collapsed into one event. A failure count without a
later guidance-tree change reports
`PRODUCED_WITHOUT_POST_FAILURE_GUIDANCE_CHANGE` and cannot satisfy liveness.

The four evolved-cell statuses are, in ordinal order,
`PRODUCED_NOT_SELECTED_LATER`, `GUIDANCE_PRODUCED_AND_SELECTED_LATER`,
`NO_GUIDANCE_PRODUCED`, and `PRODUCED_WITHOUT_LATER_OPPORTUNITY`. This gives one
valid local production/admission/later-selection chain, but the blocking
checker-runtime defect above prevents classifying DEV-002 as a clean matrix or
authorizing Sol replication. The tracked execution record is
`stage5a_review/dev002-execution-audit.json`.

DEV-003 retains the same declared 12-cell scientific shape only for a possible
future clean run. It has zero completed cells and zero model sessions. Its
machine-review record `stage5a_review/dev003-audit.json` establishes protocol
identity, clean-source reproducibility, exact-runtime preflight, fail-closed
evidence, and zero formal state only; it contains no produced/admitted/selected
guidance result.

## Gates before a real Mathlib-style experiment

1. Retain actual Phase 4 Linux hard-gate evidence for the same frozen public
   hashes, including OS/architecture, Lean/Mathlib identity, command, exit
   status, and log hashes.
2. Complete qualified, independent human review and retain its record under
   private custody. Existing AI-agent annotation is not human review.
3. Pass a new Phase 5 readiness audit; do not rewrite the existing failed audit
   into a pass.
4. Standardize a reproducible default Python dependency entrypoint, including
   the pinned `jsonschema` overlay required by the Phase 4 harness.
5. Define independent train, development, and evaluation splits grouped to
   prevent theorem-, module-, and source-PR leakage.
6. Physically isolate workers from the private evaluator, gold, provenance,
   adjudication, and all answer-revealing score intermediates. Hook and prompt
   instructions alone are not physical isolation.
7. Prove that prompts, logs, populations, guidance, reference candidates,
   scores, crashes, retries, caches, and resume/import state cannot leak private
   material across conditions or runs.
8. Freeze budgets, concurrency, provider/model identity, timeouts, failure and
   retry policy, boundary handling, and stopping conditions before unsealing
   evaluation data.
9. Compare static/no-evolution, fixed-initial-guidance, and EvE conditions under
   the same tasks, model substrate, context, tool access, and compute budget.
10. Use at least two independent random seeds per condition and predeclare how
    stochastic results will be summarized.
11. Preserve formal REPAIR hard gates: compilation, placeholders/trusted
    declarations, warning allow-lists, target issue resolution, no new blocking
    findings, statement/specification preservation, axiom deltas, hashes, and
    deterministic scoring.
12. Treat smoke success only as harness evidence. Never use it as a benchmark,
    scientific, performance, or model-capability conclusion.

## Current blockers inherited from Phase 4/5

The repository's readiness audit remains `blocked-by-phase4-readiness` because
the frozen pilot lacks actual Linux evidence and qualified independent human
review. The default Python runtime also lacks the pinned Phase 4 `jsonschema`
dependency unless the documented overlay is used. Those blockers are not
changed by this sidecar.

## Stage 1 threat-model limitations

For this public smoke, the evaluator is external to the candidate and EvE's
workspace boundary plus post-evaluation protected hashes provide defense in
depth. This is not an OS-level security boundary against arbitrary hostile Lean
metaprograms. A real private evaluation requires a separate account/container
or equivalent isolation with one-way candidate transfer and sanitized score
return. Until that architecture exists and is tested, private gold must remain
disconnected.
