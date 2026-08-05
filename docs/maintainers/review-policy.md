# Review and commit policy

## Commit scope

Each non-merge commit must change exactly one repository file. A commit may add
at most one Lean `structure` or `class` declaration.

When a commit introduces a structure or class, all newly introduced definitions,
theorems, and functions that construct it, use its fields, or state its
intermediate or important results must remain in that same Lean module. A later
commit may refactor a mature API only with an explicit justification in its
commit message and pull-request description.

The CI check enforces the one-file and one-new-structure/class rules. Code review
checks the semantic same-module rule, because it requires understanding Lean
types and the intended mathematical API.

### Historical exceptions

The branch history contains four immutable commits that predate enforcement
or establish the imported EFG review baseline:

- `8f2009531d0e71f3891b732bffdf1731414d2640`
- `ad4ebea4dbb84ef91d9e0fdc4d7356f9e22cd6f8`
- `c42e9b0d7a610c11bd596f71b339b78de6944b74`
- `69368f1a18534c8abb5f6c20e8154b48af57abe8`

CI passes these exact SHAs through repeated `--grandfather-commit` arguments.
The exception is equality-based, not an ancestry cutoff: no descendant, new
merge, or later multi-file commit is exempt. Adding another exception is a
review-policy change and requires a written repository-history reason.

## Naming

All Lean declarations must follow the
[Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html).
In particular, use American English; use `UpperCamelCase` for types, structures,
classes, and propositions; use `snake_case` for theorem and proof names; and use
`lowerCamelCase` for non-`Prop` terms. Follow Mathlib's established structural
lemma patterns such as `.ext`, `.ext_iff`, `*_injective`, and `*_of_*` whenever
they apply.

Code review should request a concrete Mathlib-style alternative when a name is
not compliant, rather than making a purely stylistic comment.
