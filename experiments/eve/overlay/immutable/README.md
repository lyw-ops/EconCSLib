# EconCSLib Mathlib-style REPAIR plumbing smoke

This is a public synthetic Stage 0 plumbing smoke, not a benchmark case and
not evidence of model capability. The only solver edit permitted is the exact
file listed below. Formal evaluation, configuration, manual, seed baseline,
and scoring code are outside the solver workspace and are off-limits.

## Required workflow

1. Read the immutable `MANUAL_EN.md`; it is the normative style authority.
2. Read the candidate declaration and the general files under `guidance/`.
3. Make the smallest justified repair without changing the public declaration
   or its meaning.
4. Do not treat compilation alone as style acceptance. Inspect any output from
   permitted local checks and remove all unexpected warnings.
5. Do not use `sorry`, `admit`, a new `axiom` or `constant`, `unsafe`,
   `opaque`, native-code trust shortcuts, linter disabling, or trusted bypasses.
6. Do not read or seek any evaluator, gold, provenance, score, or
   `heldout/private/` content. If context is insufficient, record that fact
   rather than guessing.
7. Before finishing, run the boundary command below. Do not attempt to modify
   its implementation.

## Solver edit contract

Editable files:

{editable_files_block}

Editable folders:

{editable_folders_block}

All other solver paths are immutable. The optimizer may refine only general
guidance under `guidance/`; it must not encode a case-specific answer.

## Boundary check

```bash
{{BOUNDARY_CHECK_COMMAND}}
```

The formal deterministic evaluator runs after the worker finishes. Its source
and results are deliberately unavailable to the worker.

