Restore the two exact edit surfaces: `solver/Candidate.lean`, plus
`guidance/docs/learned.md` only when it records a concise, general principle
written after an actual recorded Lean failure. Revert every other changed
path, then run `/usr/bin/python3 STAGE5A_LEAN_CHECK.py`; the final checker event
must match the final candidate.
