# Mathlib Style Benchmark Phase 4 runbook

Phase 4 is an internal pilot over 16 primary cases and six PAIR A/B mirrors. The public
inventory is frozen by `manifests/PUBLIC_SHA256.json`; ignored private custody material is
kept below `heldout/private/` and is never required by the public CI job.

## Public validation

Install the frozen JSON Schema runtime and run the public gates from the repository root:

```bash
python3 -m pip install --requirement benchmarks/mathlib-style/requirements-phase4.txt
python3 -m unittest discover -s benchmarks/mathlib-style/tests -v
python3 benchmarks/mathlib-style/scripts/check_benchmark.py
python3 benchmarks/mathlib-style/scripts/check_phase4_preservation.py
```

`check_benchmark.py` retains the Phase 2/3 fixture and distillation checks, then invokes
`phase4_harness.py`. The Phase 4 harness uses a local Draft 2020-12 schema registry, checks
the 6/4/3/3 task matrix and four 4-case strata, verifies all PAIR mirrors, scans public files
for private/source leakage, rejects generated Lean artifacts, runs the static placeholder and
native-backend guard, compiles every wrapper twice with a timeout, captures normalized
warnings, runs the Mathlib standard and text/Unicode linter suites, and runs a
declaration-level `#print axioms` probe.

On Linux, `.github/workflows/mathlib-style-phase4.yml` additionally runs the pinned build and
`leanchecker` through `leanprover/lean-action@v1`, records OS/architecture, Lean and Mathlib
identity, the hard-gate command, exit code, and log SHA-256 values, then uploads those records
as `mathlib-style-linux-environment-evidence`. A local Darwin pass is not a substitute for
this job.

## Private custody and blind annotation

Create two independent snapshot roots. Each root may contain only the frozen English manual,
`RULES.json`, `VALIDATORS.json`, public primary cases, the annotation/common schemas, and the
explicit v4.30 repository-context files needed by `REPOSITORY_AGENT` cases. It must not expose
source provenance, review outcomes, Gold, the other annotation, or adjudication.

Each agent writes one schema-valid `annotation.schema.json` document per primary case and sets
`saw_other_annotation` to `false`. Both complete before either output is copied into private
custody. The adjudicator then records agreements, disagreements, abstentions, confidence, and
the reason for every final choice. Gold is created only after that adjudication step.

Private repair wrappers live under `heldout/private/repairs/`. Their compiler/checker results,
warning normalization, axiom baseline/observed/delta, and declaration-type preservation result
are written as `validation-record.schema.json` documents. Raw compiler, checker, standard-linter,
text-linter, axiom-probe, and statement-probe streams stay in private logs and are linked by
SHA-256. Refresh private custody hashes only after all annotation, adjudication, Gold,
validation, and scoring artifacts are final.

Audit retained annotation isolation and provenance before executing Gold-based scoring:

```bash
python3 benchmarks/mathlib-style/scripts/check_annotation_isolation.py
python3 benchmarks/mathlib-style/scripts/check_phase4_provenance.py
```

Independent human review follows
[`HUMAN_REVIEW_RUNBOOK.md`](HUMAN_REVIEW_RUNBOOK.md). Its output stays in ignored private
custody; no human review has been recorded merely because this checklist exists.

## Scoring

Predictions must conform to the frozen v0.3.0 prediction schema:

```bash
python3 benchmarks/mathlib-style/scripts/evaluate_repairs.py \
  --predictions /path/to/predictions \
  --output benchmarks/mathlib-style/heldout/private/scoring/repair-evaluations.json
python3 benchmarks/mathlib-style/scripts/score_predictions.py \
  --predictions /path/to/predictions \
  --gold-dir benchmarks/mathlib-style/heldout/private/gold \
  --provenance-dir benchmarks/mathlib-style/heldout/private/provenance \
  --repair-evaluations \
    benchmarks/mathlib-style/heldout/private/scoring/repair-evaluations.json
```

The repair evaluator reconstructs candidate code inside the frozen wrapper and enforces the
edit region/budget, issue-resolution contract, repeat compilation, standard and text/Unicode
linters, statement type, axiom delta, warning policy, and no-new-finding gates. Reference text
match is diagnostic only. The scorer reports the 16-primary macro/micro scores separately from
the six mirrors, PAIR verdict and accepted-set accuracy, mirror consistency, DETECT
precision/recall/F1 and priority, REPAIR gate/edit-cost details, LOCATE accepted sets, global
answerability/abstention/unsupported-rationale metrics, and breakdowns by task, stratum, source
class, evaluation mode, source PR, theorem family, and module family.

## Status vocabulary

Use only the following release states:

- `human-review-pending`: two agent annotations and adjudication exist, but no independent human
  review has been recorded.
- `linux-validation-pending`: local gates pass but the actual Linux workflow has not run on the
  frozen public hashes.
- `internal-pilot-complete`: both review and Linux validation are complete for the frozen hashes.
- `public-release-eligible`: a separate release decision has approved publication and private
  custody handling.

Agent annotation never counts as human review. Do not label this pilot public-release-eligible
without an explicit release decision.
