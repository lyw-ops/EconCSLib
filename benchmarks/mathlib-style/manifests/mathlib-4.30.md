# Pinned Mathlib 4.30 Environment

This manifest is a human-readable companion to [`SOURCES.json`](SOURCES.json).
The JSON registry is authoritative for machine checks.

- Environment ID: `MATHLIB-4.30.0`
- Repository: `leanprover-community/mathlib4`
- Release: `v4.30.0`
- Commit: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- Lean toolchain: `leanprover/lean4:v4.30.0`
- Toolchain Git blob SHA-1: `af9e5d339aeb37e4e6ba2603fb873e637678e304`
- Checked date: 2026-08-13

The structural checker accepts `MATHLIB_CHECKOUT` or the repository checkout
at `.lake/packages/mathlib`, verifies the exact commit, and checks every
evidence path, Git blob SHA, and line range. The smoke compiler additionally
requires `lake env lean --version` to report Lean 4.30.0. It must not silently
substitute another Mathlib or Lean version.

The policy snapshot and future historical-case source environments are
separate identities; see
[`VERSION.md`](../../../docs/research/mathlib-style/VERSION.md).
