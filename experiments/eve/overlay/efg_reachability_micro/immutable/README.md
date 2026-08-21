# EconCSLib public Stage 1a EFG reachability micro-pilot

This is a public synthetic/local usability task. It is not a benchmark, a
completed evaluation, a model-capability claim, or evidence that EvE improved
the EFG minimal core. The evaluator, accepted fixture, hashes, configuration,
and scoring logic are outside the solver workspace.

## Required workflow

1. Read the seed `README.md`, the candidate, and `guidance/`.
2. Use only the existing StructuralCore import and declarations.
3. Preserve the fixed task data above the solver marker.
4. Add only the required local declarations to `Candidate.lean`.
5. Do not use placeholders, new axioms/constants, trusted bypasses, native
   shortcuts, linter suppression, or evaluator/gold/score material.
6. Finish with the boundary command below.

## Solver edit contract

Editable files:

{editable_files_block}

Editable folders:

{editable_folders_block}

All other solver paths are immutable.

## Boundary check

```bash
{{BOUNDARY_CHECK_COMMAND}}
```
