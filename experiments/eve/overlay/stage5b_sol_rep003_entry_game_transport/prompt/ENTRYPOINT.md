# Entry Game transport route — DEV-003

Complete every declaration required by `solver/README.md`. The candidate edit
surface is exactly `solver/Candidate.lean`; preserve the fixed exercise and
abstract theorem prefix. The separate guidance edit surface is exactly
`guidance/docs/learned.md`, and it may be changed only after an actual recorded
Lean failure. Do not edit any other path. Follow all ten immutable checkpoints
in `TRANSPORT_CHECKPOINTS.md`: construct the complete `RefinementCertificate`,
explicitly consume its Nash and SPE preservation projections, use the fixed
`AbstractTwoStage` theorems, prove encoded-profile equality reflection, and
return the exact concrete theorem signatures. A direct-only proof is not this
route.

After every candidate edit, and at least once before ending the rollout, run
`/usr/bin/python3 STAGE5A_LEAN_CHECK.py`. Missing, empty, malformed, or
candidate-mismatched check evidence fails closed. When an actual recorded Lean
failure occurs, distill one concise, generally reusable repair principle into
`guidance/docs/learned.md`; do not copy the complete proof or an exact answer.
If no recorded Lean failure occurs, do not fabricate a failure or
failure-derived guidance. A successful candidate must still return all exact
target declarations and pass the real checker.

Do not use placeholders, new trusted declarations, native shortcuts, warning
suppression, evaluator/score material, network access, or out-of-bound edits.
