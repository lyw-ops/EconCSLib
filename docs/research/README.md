# Research Notes

This directory retains selected public notes with durable mathematical or API
value. It is not a task tracker. Actionable work belongs in GitHub Issues, and
broader mathematical gaps belong in the knowledge blueprint.

The single living correctness record for the current EFG implementation is
`efg_strict_correctness_audit.md`. Current API navigation and lifecycle status
are maintained under `../design/`, especially `efg-public-api.md`,
`efg-governance.md`, and `efg-module-status.md`. Historical cycle audits,
completed execution plans, migration trackers, and private extraction reports
are intentionally not retained.

## Notes

- `design_decisions.md`: architectural rationale that still explains the code.
- `arrow_proof_source.md`: source comparison for the Arrow proof.
- `chapter7_formalization_audit.md`: semantic comparison of the implemented
  Chapter 7 correlated-equilibrium, learning, and Bayesian-game APIs with
  MFoGT.
- `infinite_game_inductive.md`: extensive-game modeling notes.
- `extensive_game_architecture.md`: theorem-driven architecture and proof
  routes for history-indexed EFGs, augmented information, and representation
  transfer.
- `efg_simulation_framework_status.md`: verified theorem inventory and current
  boundary of the simulation-oriented EFG framework.
- `efg_strict_correctness_audit.md`: living declaration-level correctness
  matrix, regressions, verification evidence, axiom checks, residual risks,
  and red-team readback for the current EFG implementation.
- `lean_pitfalls.md`: reusable Lean and Mathlib implementation notes.
- `minimax_comparison.md`: comparison of minimax proof routes.
- `minimax_general_field.md`: ordered-field minimax design.
- `minimax_proof_path.md`: minimax proof decomposition.
- `solution_concept_analysis.md`: rationale for predicate-based solution
  concepts.
- `zerosum_assumptions.md`: minimal assumptions for zero-sum definitions and
  theorems.
