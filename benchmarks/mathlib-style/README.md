# Mathlib Style benchmark assets

This tree integrates the v0.3.1 machine registries, pinned evidence, synthetic smoke
fixtures, the Phase 4 formal pilot, held-out policy, and validation scripts.
Read the [normative English manual](../../docs/research/mathlib-style/MANUAL_EN.md)
and the local [`AGENTS.md`](AGENTS.md) before working here.

Phase 3 normative revision is complete for the rule/manual artifact `v0.3.1`,
including all 13 P1/P2 findings from the immutable Phase 2 audit. The Phase 4
pilot identity is independently versioned as `MATHLIB-STYLE-PILOT-0.1.0`; its
16 primary cases and 6 PAIR mirrors pass the local hard gates. The complete
[v0.3.0 JSON Schemas](manifests/schemas/README.md), 75 leaf IDs, legacy aliases,
task definitions, and original smoke fixtures remain unchanged. This is not a
published benchmark: actual Linux validation and human review remain pending.

## Layout

- `manifests/`: frozen rules, sources, validators, coverage, environment
  identity, and schema inventory;
- `evidence/`: retrieval indexes and pinned evidence anchors;
- `fixtures/positive/`: accepted Mathlib-style smoke examples;
- `fixtures/negative/`: compilable smoke examples with annotated findings;
- `fixtures/repair/`: before/after smoke repairs;
- `cases/pair/`, `cases/detect/`, `cases/repair/`, and `cases/locate/`: public
  formal pilot prompts, including separately counted PAIR mirrors;
- `heldout/`: committed custody policy only; ignored private gold, provenance,
  annotations, adjudication, validation, logs, and release manifests stay
  under `heldout/private/`;
- `scripts/`: structural validation, strict static guards, the Phase 4 hard-gate
  harness, executable REPAIR evaluation, provenance/annotation isolation audits,
  environment evidence, deterministic task scoring, and preservation checks;
- `reports/phase4/`: the public baseline inventory, runbook, and
  [pilot report](reports/phase4/PILOT_REPORT.md).

Every visible fixture lives in its own directory with `case.json` plus the Lean
files named by `compile_files`. Fixture kind does not replace `task` metadata,
and `evaluation_scope` says whether the whole file, a declaration, or an
expression is being judged. Packaging outside that scope is not benchmark
gold. Current fixtures use `status: SYNTHETIC_SMOKE`; they exercise repository
and compiler checks but cannot support a natural-PR pilot score or a model
capability conclusion.

A visible fixture manifest minimally contains:

- stable `id`, `kind`, `task`, `status`, and `source_class`;
- evaluation and policy snapshot references;
- `compile_files`, `evaluation_scope`, and target leaf-rule IDs;
- warning expectation and a short purpose statement.

Formal benchmark cases must additionally separate public prompt, private gold,
private provenance, and validation records; record base/merge commits, license,
source review, porting changes, hashes, warnings, axiom delta, and
statement-preservation evidence; and receive independent annotation and
adjudication.

## Task union

- `PAIR` compares A/B and returns `A`, `B`, `TIE`, or
  `INSUFFICIENT_CONTEXT`.
- `DETECT` identifies declaration-aware, leaf-rule-level findings.
- `REPAIR` makes a minimal change inside an explicit edit contract.
- `LOCATE` chooses among supplied homes or reports missing context.

Public prompts do not contain answerability labels or source identifiers that
reveal gold. Private answerability is `ANSWERABLE`, `MULTIPLE_ACCEPTABLE`, or
`INSUFFICIENT_CONTEXT`. A repository-agent evaluation may inspect the pinned
checkout; a closed-context evaluation may not. Report the two modes separately.

## Findings and repairs

Every finding records a leaf `rule_id`, rule strength, case-specific review
priority, declaration-aware line/column span, evidence, and rationale. New gold
must not target legacy mixed aliases.

A repair case freezes non-editable declarations and states whether imports,
new declarations, or renaming are allowed. It also defines a statement or
specification-preservation contract, change budget, and edit-cost metric.
Reference repairs are diagnostic; exact textual match is not the primary score.

## Validation gates

Final candidates must:

1. compile in the pinned environment;
2. contain no `sorry` or `admit`;
3. introduce no `axiom` or `constant`;
4. have no target-declaration axiom delta from baseline;
5. have no warning outside the case allow-list;
6. pass all claimed statement/specification-preservation checks;
7. link source, metadata, logs, and validation records by SHA-256.

The Phase 4 harness implements full Draft 2020-12 schema validation with local
`$ref` resolution, recursive public/private leakage and hash checks, one
compiler/text-linter temporary subtree per case, repeat compilation, the Mathlib
standard and text/Unicode linters, static forbidden-construct guards, declaration
axiom probes, warning allow-lists, applicable `#find_home` evidence, executable
REPAIR statement-preservation checks, and validation-record generation. The
scorer is deterministic and task-aware; it does not use an LLM judge.

Run it from the repository root:

```bash
python3 benchmarks/mathlib-style/scripts/check_distillation.py
python3 benchmarks/mathlib-style/scripts/check_benchmark.py
```

## Metrics and split policy

- PAIR: verdict accuracy, accepted-set accuracy, and mirror consistency.
- DETECT: finding-level rule F1 and span overlap.
- REPAIR: compilation, issue resolution, interface preservation, new findings,
  and edit cost.
- LOCATE: accepted-location accuracy and support rate.
- Global: answerability, unsupported-rationale rate, abstention calibration,
  and results stratified by source class, stratum, and evaluation mode.

Primary deterministic scores do not use an LLM judge. Group splits by source
PR, theorem family, and module family to reduce leakage. Assign difficulty only
after the pilot, using annotation time, disagreement, repository context, and
baseline behavior.

## Phase 4 pilot status

The pilot has exactly 16 real primary cases: PAIR 6, DETECT 4, REPAIR 3,
LOCATE 3, balanced 4/4/4/4 across surface, documentation/statement, proof, and
API/integration strata. Six PAIR mirrors are excluded from the primary count.
Private custody contains complete provenance, two independent AI-agent blind
annotations, adjudication, executable repairs, validation records, and gold.

Local validation is complete. Release still requires an actual pinned Linux
run and human review, so the status is `linux-validation-pending` and
`human-review-pending`, not complete. See the
[Phase 4 pilot report](reports/phase4/PILOT_REPORT.md) and the
[completion-status report](../../docs/research/mathlib-style/PHASE4_COMPLETION_REPORT.md).
