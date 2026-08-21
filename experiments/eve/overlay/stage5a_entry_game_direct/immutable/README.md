# Public Stage 5A development task: Entry Game direct route

This is a public, answer-visible development experiment, not a hidden
benchmark. Prove the exact direct-route declarations in `solver/README.md`.

{editable_files_block}
{editable_folders_block}
The two edit surfaces are distinct: the solver candidate surface is exactly
`solver/Candidate.lean`; the optimizer-guidance surface is exactly
`guidance/docs/learned.md` and is available only after a recorded failing Lean
check. Do not edit any other path.
Use this command after every change to the candidate:

```bash
python3 STAGE5A_LEAN_CHECK.py
```

The command performs a real local Lean check and records its exit status. If a
recorded check fails, use the actual error to add one short, reusable repair
principle under `guidance/`. The principle must be useful beyond this exact
proof and must not copy the final proof. If no recorded check fails, do not
invent a failure and do not add purported failure-derived guidance.

Boundary check:

```bash
{{BOUNDARY_CHECK_COMMAND}}
```
