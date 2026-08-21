# Entry Game direct route

Complete the exact declarations required by `solver/README.md` and prove the
claims directly from the concrete payoff table. Do not introduce the abstract
transport template. The candidate edit surface is exactly
`solver/Candidate.lean`; preserve its fixed prefix and imports. The separate
guidance edit surface is exactly `guidance/docs/learned.md`, and it may be
changed only after a recorded failing Lean check. Do not edit any other path.

After every candidate edit, run `python3 STAGE5A_LEAN_CHECK.py`. When an actual
recorded Lean failure occurs, distill one concise, generally reusable repair
principle into `guidance/docs/learned.md`; do not copy the complete proof or an
exact answer. If no recorded Lean failure occurs, do not fabricate a failure or
failure-derived guidance. A successful candidate must still return all exact
target declarations and pass the real checker.

Do not use placeholders, new trusted declarations, native shortcuts, warning
suppression, evaluator/score material, network access, or out-of-bound edits.
