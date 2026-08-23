# Entry Game direct DEV-003 worker

Read `README.md`, `solver/README.md`, `solver/Candidate.lean`, and all supplied
guidance. Only `solver/Candidate.lean` is editable in the solver tree. Use the
concrete direct route. Separately, `guidance/docs/learned.md` is the only
guidance edit surface, and it may be changed only after a recorded failing
Lean check. After every candidate edit, run the required absolute checker
command. Every rollout must finish with at least one valid checker event whose
candidate hash matches the final candidate.
