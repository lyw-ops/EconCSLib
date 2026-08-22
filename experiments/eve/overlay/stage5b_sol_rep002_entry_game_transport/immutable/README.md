# Public Stage 5A DEV-003 task: Entry Game transport route

This is a public, answer-visible development experiment, not a hidden
benchmark. Complete the exact refinement-certificate and conclusion-transport
declarations in `solver/README.md`, following all ten checkpoints in
`TRANSPORT_CHECKPOINTS.md`.

{editable_files_block}
{editable_folders_block}
The two edit surfaces are distinct: the solver candidate surface is exactly
`solver/Candidate.lean`; the optimizer-guidance surface is exactly
`guidance/docs/learned.md` and is available only after a recorded failing Lean
check. Do not edit any other path.

Use this exact Python 3.9.6 command after every change to the candidate and at
least once in every rollout:

```bash
/usr/bin/python3 STAGE5A_LEAN_CHECK.py
```

The command runs real Lean and records its stdout, stderr, exit status,
checker hash, candidate hash, guidance hash, Python identity, and a contiguous
event chain. The final event must match the final candidate; missing, empty,
malformed, or mismatched evidence fails the rollout. If a recorded check
fails, use the actual error to add one short, reusable repair principle under
`guidance/`. The principle must be useful beyond this exact proof and must not
copy the final proof. If no recorded check fails, do not invent a failure or
add purported failure-derived guidance.

Boundary check:

```bash
{{BOUNDARY_CHECK_COMMAND}}
```
