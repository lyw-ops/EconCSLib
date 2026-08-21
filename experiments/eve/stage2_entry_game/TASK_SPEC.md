# Stage 2 Entry Game paired micro-task

Task ID: `EVE-ENTRY-GAME-PAIRED-001`

Both routes use the exact source lock in `source-lock.json` and must establish
the same two claims:

1. the unique pure subgame-perfect profile is `(enter, acquiesce)`;
2. `(stayOut, fight)` is Nash but not subgame-perfect.

The direct route proves these facts by inspecting the concrete payoff table.
The transport route must encode the exercise into the fixed abstract
two-stage template, construct the `RefinementCertificate`, establish the
strict-entry hypothesis bridge, apply `AbstractTwoStage.unique_spe_of_strict`,
and transport the conclusion back to the exercise profile.

The paired package is accepted only when both deterministic route evaluators
pass and the agreement evaluator confirms the same source lock, target claims,
environment, and independent route boundaries.

This is a public development task. Its fixtures and mutations are not private,
and Codex review is not independent human review.
