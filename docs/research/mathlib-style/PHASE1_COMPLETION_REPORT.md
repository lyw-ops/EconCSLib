# Mathlib Style Distillation Phase 1 Completion Report

- **Date:** 2026-08-13
- **Outcome:** Complete
- **Scope:** Repository integration
- **Benchmark status:** Incomplete and unpublished

## 1. Outcome

Phase 1 is complete. The documentation and benchmark directories were
integrated, the complete v0.3.0 schema set was recovered from a verifiable
artifact, and the static checks, standard JSON Schema validation, and pinned
Lean/Mathlib smoke compilation passed. The legacy root
`mathlib-style-distillation/` directory was removed only after the before/after
migration comparison and validation passed.

This conclusion applies only to repository integration. It does not claim that
the formal benchmark, pilot, or full harness was complete at this phase.

## 2. Delivered layout

The phase introduced:

- `docs/research/mathlib-style/` for the normative manual, taxonomy,
  decisions, version metadata, and integration reports;
- `benchmarks/mathlib-style/` for agent instructions, evidence indexes,
  task-policy directories, smoke fixtures, held-out custody policy,
  registries, schemas, and validation scripts;
- a short Mathlib-style entry in the repository-level `AGENTS.md`.

The schema directory contains 11 verbatim `*.schema.json` files, a manifest
with the source byte counts and SHA-256 values, and a provenance README.

The old untracked root `mathlib-style-distillation/` directory was deleted
after verification. No staging, commit, push, or pull request occurred during
the original Phase 1 work.

## 3. Preserved invariants

| Invariant | Result |
|---|---:|
| Unique leaf rule IDs | 75 |
| Naming rules | 12 |
| Statement rules (`FMT-*`, `STM-*`) | 24 |
| API rules | 7 |
| Proof rules | 7 |
| Documentation rules | 13 |
| Import/file-structure rules | 12 |
| Rule strengths | `MUST/SHOULD/PREFER/CONTEXT` |
| Finding priorities | `BLOCKING/SUBSTANTIVE/MINOR/INFORMATIONAL` |
| Task union | `PAIR/DETECT/REPAIR/LOCATE` |
| Evidence anchors | 10 |
| Synthetic smoke fixtures | 3 |
| Lean fixture files | 4 |
| Frozen schemas | 11 |

Pinned identities:

- Mathlib `v4.30.0` at
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`;
- Lean `leanprover/lean4:v4.30.0`;
- policy snapshot `MATHLIB-POLICY-2026-08-13` at
  `7b967eb1aaab674bd6aead708d42c4a83e2aca05`.

The migration comparison confirmed the same 75 rule IDs, the same registry
semantics, 10 unchanged evidence records after reclassification, unchanged
smoke fixtures and held-out policy, and 11 schema files byte-identical to the
source artifact.

## 4. Validation

The structural and integrity check was:

```bash
python3 benchmarks/mathlib-style/scripts/check_distillation.py
```

It covered layout, registries, rule vocabulary, task union, manual/taxonomy
coverage, evidence-index partitioning, Markdown links, schema hashes and local
references, evidence commit/blob/line ranges, fixture metadata, held-out
custody, and the static guard.

Standard `jsonschema==4.25.1` Draft 2020-12 validation checked all 11 schemas
against their metaschema and validated the 12 examples supplied with the
source artifact. The temporary validator did not become a repository
dependency.

Pinned smoke compilation was run with:

```bash
python3 benchmarks/mathlib-style/scripts/check_benchmark.py
```

All three smoke cases and four Lean files compiled with Lean 4.30.0 and no
unexpected warnings. JSON/JSONL parsing and `git diff --check` also passed.

## 5. Phase boundary

Phase 1 had no unresolved integration blocker. The following remained later
work rather than Phase 1 blockers:

- an adversarial audit of the manual;
- the complete style-linter, axiom, warning, preservation, and scoring harness;
- 16 formal pilot cases;
- two independent annotations and adjudication;
- baseline model evaluation.

The phase did not modify or clean existing EFG source, documentation, scripts,
or unrelated worktree changes. It did not claim that the Mathlib Style
Benchmark was complete or published.

## 6. English-only packaging note

On 2026-08-14, the repository moved the report to this English,
language-neutral path as part of an English-only packaging migration. That
migration did not change the historical Phase 1 outcome or the frozen rule and
schema identities.
