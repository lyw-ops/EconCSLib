# Mathlib Style Distillation

This directory contains the human-readable v0.3.1 Mathlib Style specification
and repository-integration/audit notes. Machine-readable registries, evidence,
fixtures, and smoke-validation scripts live under
[`benchmarks/mathlib-style/`](../../../benchmarks/mathlib-style/README.md).

## Authority and modes

In **Evaluation Mode**, [`MANUAL_EN.md`](MANUAL_EN.md) is the normative
specification and the repository distributes no translated manual.
[`TAXONOMY.md`](TAXONOMY.md) is a human-readable index; rule identity remains defined by
[`RULES.json`](../../../benchmarks/mathlib-style/manifests/RULES.json).

In **Distillation/Audit Mode**, judgments about the manual must be supported by
the pinned Mathlib source tree, the independently pinned policy snapshot, and
pinned validator behavior. The manual cannot be used to prove its own
correctness. Counterexamples must be classified independently from rule
strength and finding priority before any later rule revision is proposed.

## Maturity

Phase 3 normative revision is complete for the rule/manual artifact `v0.3.1`.
It resolves all 13 P1/P2 findings in the immutable Phase 2 adversarial audit
without changing the 75 leaf IDs, legacy aliases, task definitions, environment
pins, policy pins, or any benchmark data schema. The complete 11-file JSON
Schema set remains byte-for-byte frozen at `v0.3.0`.

Phase 4 has produced a separate `MATHLIB-STYLE-PILOT-0.1.0` artifact with 16
real primary cases, 6 PAIR mirrors, isolated private custody, two independent
AI-agent blind annotations, adjudication, a full local hard-gate harness, and
deterministic scoring. This does not change the rule/manual or schema versions.
The benchmark is still not published: actual pinned Linux validation and human
review remain pending, so no model-capability or public-release claim is made.
Schema provenance and exact hashes are recorded in the
[`schemas` manifest](../../../benchmarks/mathlib-style/manifests/schemas/MANIFEST.json),
with migration status in [`VERSION.md`](VERSION.md).

The benchmark continues to require answerability metadata, axiom
baseline/observed/delta checks, compiler-warning allow-lists,
statement/specification preservation, provenance, content hashes, and pinned
environment validation before formal cases can be accepted.

## Files

- [`MANUAL_EN.md`](MANUAL_EN.md): normative Evaluation Mode specification.
- [`TAXONOMY.md`](TAXONOMY.md): exact 75-rule human-readable taxonomy.
- [`DECISIONS.md`](DECISIONS.md): packaging and evaluation decisions.
- [`VERSION.md`](VERSION.md): independent version identities and migration
  status.
- [`REPOSITORY_INTEGRATION.md`](REPOSITORY_INTEGRATION.md): architecture
  conclusion, Phase 1 completion status, validation, and scope boundary.
- [`PHASE1_COMPLETION_REPORT.md`](PHASE1_COMPLETION_REPORT.md): auditable
  Phase 1 outcome, changed paths, invariants, validation, and scope confirmation.
- [`manual_adversarial_audit.md`](../../../benchmarks/mathlib-style/evidence/audits/manual_adversarial_audit.md):
  immutable Phase 2 audit of the `v0.3.0` manual/rules artifact.
- [`PHASE3_COMPLETION_REPORT.md`](PHASE3_COMPLETION_REPORT.md): Phase 3
  finding disposition, version boundary, changed/unchanged paths, validation,
  and Phase 4 handoff.
- [`PHASE4_COMPLETION_REPORT.md`](PHASE4_COMPLETION_REPORT.md): Phase 4
  pilot construction, custody, annotation, harness, local validation, and
  outstanding Linux/human gates.

Run validation from the repository root:

```bash
python3 benchmarks/mathlib-style/scripts/check_distillation.py
python3 benchmarks/mathlib-style/scripts/check_benchmark.py
```

The second command preserves the original smoke checks and also invokes the
Phase 4 public hard gates. Private custody validation is run explicitly through
the Phase 4 harness as documented in the pilot runbook.
