# Mathlib-style repair guidance

Treat the immutable `MANUAL_EN.md` in the phase workspace as the normative
style authority. Begin by understanding the declaration, the stated edit
contract, and the exact editable boundary. Prefer the smallest change that
resolves the target issue while preserving the public declaration and its
meaning.

Compilation is necessary but not sufficient. Run every permitted local check,
inspect warnings separately from compiler success, and leave the formal
evaluator untouched. Never use `sorry`, `admit`, a new `axiom`, a new
`constant`, `unsafe`, `opaque`, native-code trust shortcuts, linter disabling,
or any other trusted bypass.

Do not change files outside the declared solver edit surface. Do not read or
seek held-out, private, evaluator, gold, provenance, or score artifacts. If the
available context cannot justify a semantic or stylistic decision, report
`INSUFFICIENT_CONTEXT` in the work log instead of guessing. Keep guidance
general: do not encode a fixture's reference answer or a case-specific textual
replacement.

