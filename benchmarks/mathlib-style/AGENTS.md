# Mathlib Style Distillation Agent Guide

## Mathlib version

All style judgments in this repository target Mathlib `v4.30.0`, commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, with Lean
`leanprover/lean4:v4.30.0`.

Do not silently transfer a judgment to another Mathlib version. Record a new
environment snapshot first.

## Normative style specification

Before evaluating or generating Lean code, read:

`../../docs/research/mathlib-style/MANUAL_EN.md`

Treat it as the sole normative style specification. The repository distributes
English-only Mathlib-style assets. When the manual and a machine-readable rule
disagree, stop and record the discrepancy in
`../../docs/research/mathlib-style/DECISIONS.md`; do not silently choose one.

## Evidence

Use `manifests/RULES.json` for leaf-rule metadata and `manifests/SOURCES.json`
for pinned source identities. The six retrieval indexes preserve the five
legacy category groups, with declarations split into statements and API; they
are not separate authorities.

When citing Mathlib code, include the pinned commit, repository-relative file,
line or declaration anchor, applicable leaf rule, and a short explanation.
A concrete example is evidence for a judgment, not proof of a universal rule.
Distinguish direct manual requirements, pinned validator behavior, review
heuristics, and synthesized guidance.

## Core requirements

When generating or reviewing Lean code:

1. Prefer existing Mathlib abstractions and APIs.
2. Follow Mathlib naming conventions.
3. Prefer canonical theorem statements.
4. Avoid unnecessary assumptions.
5. Avoid unnecessary explicit arguments.
6. Prefer idiomatic Mathlib proof structure.
7. Keep declarations at the appropriate level of generality.
8. Do not optimize merely for shorter proofs.
9. Distinguish semantic correctness from stylistic conformity.
10. Cite concrete, pinned Mathlib examples when making style judgments.

## Evaluation

For every style-violation report:

- identify one or more leaf rule IDs;
- give the relevant declaration and file span;
- explain the evidence and why the rule applies;
- propose a minimal Mathlib-style repair;
- report rule strength separately from case-specific review priority;
- distinguish objective validator failures from heuristic preferences;
- state `INSUFFICIENT_CONTEXT` when the available context cannot decide the
  issue reliably.

Do not target legacy mixed aliases in new annotations.

## Benchmark handling

`fixtures/positive/`, `fixtures/negative/`, and `fixtures/repair/` contain
visible development data. `heldout/` must not contain committed answer keys, provenance
that reveals an answer, or generated predictions. Do not tune rules or prompts
against held-out outcomes.

Formal cases live under task-organized `cases/pair/`, `cases/detect/`,
`cases/repair/`, and `cases/locate/`. Do not use positive/negative as their
primary public layout or commit private answerability, gold, provenance, or
validation metadata beside public prompts.

Synthetic smoke cases test the harness; they are not a substitute for natural,
traceable Mathlib PR cases. Preserve source licenses and record porting changes
for every mined case.

## Verification

Do not mark Lean code as accepted merely because it compiles. Check separately:

- correctness and statement preservation;
- placeholder and axiom policy;
- compiler warnings and pinned validators;
- API usage and theorem-statement design;
- naming and proof style;
- documentation, placement, and maintainability.

For repository changes, run:

```bash
python3 benchmarks/mathlib-style/scripts/check_distillation.py
python3 benchmarks/mathlib-style/scripts/check_benchmark.py
```

The smoke harness does not yet implement every hard-validation gate in the
manual. Never describe it as the final benchmark harness.
