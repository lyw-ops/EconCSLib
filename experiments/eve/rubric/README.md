# EVE rubric R000: deterministic shadow instrumentation

R000 is the first machine-readable seed for studying future rubric evolution.
It instruments the existing public Stage 2 Entry Game evaluator; it does not
change mathematical acceptance, execute EvE, or claim that a rubric has
self-evolved.

## Authority boundary

The trusted hard oracle remains
`experiments/eve/scripts/evaluate_stage2_entry_game.py` byte-for-byte. Its
binary rule is authoritative:

- every hard gate passes: hard score `1.0`, accepted;
- any hard gate fails: hard score `0.0`, rejected.

`shadow_search_score` is separately labelled
`non-authoritative-shadow-only`, `does-not-control-selection`, and
`not-mathematical-acceptance`. It never changes `score.yaml`, cannot compensate
for a hard failure, and is not connected to EvE candidate selection. Only the
old evaluator can set `hard_accepted=true`.

The additive adapter calls the old evaluator's read-only Python interface. The
candidate is materialized outside the repository, while Lean's evaluator-local
compilation files live in a disposable directory under this new `rubric/`
namespace because Lean requires inputs beneath the Lake project root. That
directory is deleted after each call. Nothing is written to the historical
`experiments/eve/.runtime` tree. The canonical legacy report is represented by
its SHA-256 in every shadow result.

## R000 source and limitations

`versions/R000.json` derives from the tracked Stage 3 rubric and review plus
the Stage 2 cases, mutation corpus, evaluator, and shared evaluator helpers.
Their repository-relative paths and SHA-256 hashes are recorded in
`artifact_sources`; `versions/R000.sha256` hashes the canonical, key-sorted
JSON representation of the registry.

R000 is a seed over one answer-visible public development pair. It is not a
new Gold, hidden evaluation, benchmark, generalization result, causal EvE
result, or model-capability result. The Stage 3 record is Codex AI review, not
independent human review. DEV-003 candidates exist only in untracked local
runtime evidence and cannot be replayed from GitHub; this implementation does
not fabricate trajectory replay.

## Criterion registry

Each criterion has a stable ID, bilingual name, description, applicability,
prerequisites, evidence sources and strength, severity, score role, and
protection flag. The namespaces are:

- `CORE.*`: mirrors common deterministic hard-gate progress;
- `DIRECT.*`: concrete-route proof obligations;
- `TRANSPORT.*`: encoding, certificate, preservation, theorem-use, and
  conclusion-transport obligations;
- `PAIRED.*`: shared-source, target, workspace, and route-agreement obligations.

Evidence strengths distinguish Lean-kernel contracts, deterministic contracts,
static checks, syntactic-only observations, and review-only claims. Natural
language review is never converted automatically into `PASS`. Token presence
does not prove mathematical use. In particular, transport obligations supported
only by route tokens remain `UNKNOWN` even when the old route-discipline gate
passes. `review_only` and semantic `syntactic_only` criteria are
`diagnostic_only` and excluded from the shadow score.

## Obligation graphs

The JSON graphs in `obligation_graphs/` cover core, direct, transport, and
paired packages. Route graphs inherit the core graph; the paired graph inherits
all three component graphs. Every edge is a real criterion prerequisite,
every prerequisite exists, and validation rejects either graph-inheritance or
criterion cycles. `CORE.PROTECTED_ASSETS_FINAL` deliberately has no prerequisite
because the legacy `_report` function evaluates it on every early-return path.

## Obligation status semantics

Every result uses exactly one of five statuses:

- `PASS`: reliable deterministic evidence directly establishes the criterion;
- `FAIL`: an executed check and mapped failure code identify this criterion as
  failed;
- `NOT_EVALUATED`: fail-fast returned before this criterion ran;
- `NOT_APPLICABLE`: the criterion belongs to another route/package;
- `UNKNOWN`: available evidence cannot safely distinguish pass from failure or
  cannot establish the semantic claim.

`UNKNOWN` is intentional, not a weak pass. It is used for review-only paired
claims and syntactic observations that cannot establish mathematical meaning.

## Prerequisite semantics

R000 uses strict prerequisite-consistent status propagation. A criterion cannot
receive `PASS` while an applicable prerequisite is `FAIL`, `UNKNOWN`,
`NOT_EVALUATED`, or `NOT_APPLICABLE`. R000 currently defines no
stronger-evidence prerequisite overrides. Future rubric versions may introduce
explicitly registered stronger independent-evidence overrides, but an override
must name the exact criterion/prerequisite pair and none exists in R000.

The runtime invariant checks every generated obligation package as well as the
static DAG. `PAIRED.SAME_MATHEMATICAL_TARGET` remains `UNKNOWN`, so the current
`PAIRED.ROUTE_AGREEMENT` result is also `UNKNOWN`; neither paired diagnostic
controls hard acceptance. `PAIRED.SAME_SOURCE_LOCK` receives `PASS` only after
the replay reads both case manifests, compares `source_lock.id`, `.path`, and
`.sha256`, confirms the shared path is tracked, and hashes the actual locked
file. It is not hard-coded.

Every generated obligation result is validated deterministically against
`obligation-result.schema.json`. Every complete shadow result, including
accepted, ordinary-rejection, fatal-rejection, and wrapper-error outputs, is
validated against `shadow-evaluation.schema.json` before it is returned. A
schema-invalid shadow result is replaced by a schema-valid fail-closed result
with `hard_accepted=false` and `shadow_search_score=0.0`. The public replay
revalidates all two accepted and twelve mutation shadow results plus every
paired obligation before producing its report.

## Fail-fast mapping

The old evaluator initializes all gates to false, then returns at the first
blocking frontier. Consequently, a false gate is not sufficient evidence for
`FAIL`. The adapter combines the actual execution order, failure codes, route,
gate values, and report status. Its principal frontiers are:

| Legacy evidence | Criterion frontier |
| --- | --- |
| protected contract/hash failures | `CORE.PROTECTED_ASSETS_INITIAL` |
| boundary creation/deletion/modification or size | `CORE.EDIT_BOUNDARY` |
| case/seed contract failures | `CORE.SOURCE_LOCK` |
| `forbidden-import` | `CORE.IMPORT_BOUNDARY` |
| protected prefix changed | `CORE.TASK_IDENTITY` |
| forbidden construct / trusted bypass | corresponding guard criterion |
| route discipline | `CORE.ROUTE_IDENTITY` |
| toolchain, Mathlib, or Lean mismatch | `CORE.ENVIRONMENT` |
| candidate compile | `CORE.COMPILATION` |
| route contract compile | `CORE.TARGET_DECLARATIONS` |
| warning or axiom policy | corresponding policy criterion |
| final protected change | `CORE.PROTECTED_ASSETS_FINAL` |

Static and trusted-bypass checks execute as one group. Case-contract and tree
boundary checks also execute as one group. Candidate size is classified as an
edit-boundary failure but occurs after seed identity. These special cases are
encoded explicitly rather than inferred from a false gate. Unmapped evaluator
failure codes yield `UNKNOWN` and fail closed.

## Shadow frontier formula

The actual core execution sequence contains `N = 14` criteria:

```text
initial protected assets → edit boundary → source lock → import boundary
→ task identity → placeholder/trusted guards → route identity → environment
→ compilation → target declarations → warning policy → axiom allowlist
→ final protected assets
```

Let `C` be the number of consecutive `PASS` results from the beginning of that
sequence and `P` the total number of reliable `PASS` results in it. For a
nonfatal hard rejection:

```text
score = min(0.95,
            0.05
            + floor(800000 × C / N) / 1000000
            + floor(100000 × P / N) / 1000000)
```

The contiguous frontier dominates; coverage is only a stable tie-break. The
implementation uses integer micro-score arithmetic. `UNKNOWN`,
`NOT_EVALUATED`, `NOT_APPLICABLE`, and review-only evidence never count as
passes. Adding reliable passes cannot lower the score. A blocking failure in
source lock, boundary, protected assets, task identity, placeholder/trusted
bypass, or route identity forces `0.0`. Any other rejected candidate remains in
`(0.0, 0.95]`. Hard acceptance alone returns `1.0`; no hard failure can do so.

This score is only an R1 ranking baseline. It is not calibrated to success
probability or expected repair budget and uses no learned weights or LLM judge.

## Public replay

Run the complete offline replay from the repository root:

```bash
python3 experiments/eve/rubric/scripts/validate_rubric.py
python3 experiments/eve/rubric/scripts/verify_rubric_artifacts.py
python3 experiments/eve/rubric/scripts/replay_stage2_public.py \
  --rubric experiments/eve/rubric/versions/R000.json \
  --verify
```

The replay reads the old mutation manifest and materializes two accepted
candidates plus twelve mutations in a system temporary directory. It checks:

- accepted evaluated/hard accepted: `2/2`;
- mutations evaluated/hard rejected: `12/12`;
- blocking false accepts: `0`;
- expected failure codes preserved: `12/12`;
- protected source hashes and historical `.runtime` snapshots unchanged.

The checked-in JSON and Markdown reports are deterministic summaries of this
public replay. They contain no absolute paths or timestamps.

## Deliberately absent

R000 includes no rubric optimizer, LLM rubric proposer, LLM final judge,
self-rewrite loop, learned weights, private holdout, formal benchmark, mutation
mining, knowledge retrieval, new EFG task, Luna/Sol replication, or parent-child
A/B test. It does not modify the current REP-003 protocol and does not control
candidate selection.

R2 may study failure-derived rubric mutations only after this baseline is
frozen and independently reviewed. Promotion of any child rubric will require
frozen parent/child replay, shadow tests, fresh-task tests, and human
disagreement review. None of those future gates is satisfied merely by R000's
public replay.

## Review identity

The tracked self-review uses `reviewer_kind=codex-ai-review` and
`independent_human_review=false`. It checks fail-fast interpretation, the
hard/soft authority boundary, score capping, DAG validity, conservative
syntactic evidence, replay immutability, deterministic output, public-corpus
claims, model/EvE non-execution, and REP-003 non-modification. It does not
replace independent human review.
