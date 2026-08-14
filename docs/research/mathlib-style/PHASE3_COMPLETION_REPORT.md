# Mathlib Style Distillation Phase 3 Completion Report

- **Report date:** 2026-08-13
- **Status:** Complete; all 13 normative findings resolved and prescribed checks passed
- **Rule/manual artifact:** `v0.3.1`
- **Benchmark data schema:** `v0.3.0`, unchanged
- **Evaluation environment:** Mathlib `v4.30.0` at
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`, Lean
  `leanprover/lean4:v4.30.0`
- **Policy snapshot:** `MATHLIB-POLICY-2026-08-13` at
  `7b967eb1aaab674bd6aead708d42c4a83e2aca05`

## 1. Goal and scope

Phase 3 used the immutable Phase 2 adversarial audit of the v0.3.0 manual as
input. It resolved all 13 P1/P2 findings and synchronized the revisions across
the normative manual, rule taxonomy, machine-readable rule/source/validator/
coverage registries, and structural checker.

This phase was a normative patch, not a benchmark-data schema migration or
benchmark-production phase. It preserved all 75 leaf rule IDs, legacy aliases,
the `PAIR` / `DETECT` / `REPAIR` / `LOCATE` task union, and the pinned
environment and policy identities. It created no formal cases, training data,
test data, or held-out gold.

## 2. Finding disposition matrix

The strength and automation columns show `before -> after`.

| Rule | Audit disposition | Strength | Automation | v0.3.1 resolution and benchmark boundary |
|---|---|---|---|---|
| `FIL-003` | `REQUIRES_QUALIFICATION` | `SHOULD -> SHOULD` | `ASSISTED -> ASSISTED` | Sorting applies inside ordinary public and ordinary import blocks. No total order is invented for uncommon modifiers. |
| `FIL-008` | `STRENGTH_TOO_STRONG` | `MUST -> MUST` | `DETERMINISTIC -> ASSISTED` | `Mathlib.Tactic` and explicitly prohibited imports remain hard failures. `Lake.*` requires necessity, performance, and allowance review. |
| `FMT-005` | `SCOPE_TOO_BROAD` | `SHOULD -> SHOULD` | `HUMAN -> HUMAN` | Explicit types are required when omission obscures a public signature; inferable binders in typed dependent contexts remain valid exceptions. |
| `FMT-011` | `SCOPE_TOO_BROAD` | `SHOULD -> SHOULD` | `DETERMINISTIC -> ASSISTED` | Deterministic empty-line labels are limited to the pinned linter's syntax and path scope. Excluded contexts receive assisted review. |
| `FMT-012` | `REQUIRES_QUALIFICATION` | `MUST -> MUST` | `DETERMINISTIC -> ASSISTED` | The exact development, unscoped, deprecated, and debt option classes are enumerated. Other technical options require scope and necessity review. |
| `FMT-019` | `REQUIRES_QUALIFICATION` | `MUST -> MUST` | `ASSISTED -> ASSISTED` | Character and variant legality is separated from mathematical readability, and the allow-list is explicitly snapshot-dependent. |
| `DOC-001C` | `REQUIRES_QUALIFICATION` | `SHOULD -> SHOULD` | `HUMAN -> HUMAN` | Main-definition and main-statement sections are optional; notation, references, and tags are required only when relevant. |
| `DOC-002C` | `STRENGTH_TOO_WEAK` | `SHOULD -> SHOULD` | `HUMAN -> HUMAN` | New explicit fields should be documented by default, with limited generated, extends-only, and genuinely self-evident exceptions. |
| `DOC-004` | `REQUIRES_QUALIFICATION` | `SHOULD -> SHOULD` | `ASSISTED -> ASSISTED` | Mechanical docstring checks are separated from human review of punctuation, theorem emphasis, and prose. |
| `DOC-005` | `REQUIRES_QUALIFICATION` | `SHOULD -> SHOULD` | `ASSISTED -> ASSISTED` | The rule uses the real Lean 4 name `Set.mem_iUnion₂`, separates backtick formatting from name resolution, and does not claim that the planned link checker is implemented. |
| `PRF-007` | `REQUIRES_QUALIFICATION` | `MUST -> MUST` | `DETERMINISTIC -> DETERMINISTIC` | The trust prohibition remains; documented syntax-linter false negatives require the independent `lake env leanchecker --fresh Mathlib` gate. |
| `API-007` | `STRENGTH_TOO_WEAK` | `CONTEXT -> SHOULD` | `ASSISTED -> ASSISTED` | Ordinary applicable transformation parity is a `SHOULD`, while existing companions, unsupported constants, naming overrides, and API hazards remain exceptions. |
| `LOC-002A` | `REQUIRES_QUALIFICATION` | `SHOULD -> SHOULD` | `ASSISTED -> ASSISTED` | `#min_imports in` upward experiments are distinguished from incremental `linter.minImports` tracking. Neither proves global architectural minimality. |

Result: all 13 findings were incorporated into v0.3.1 normative wording and
machine metadata. No finding was deferred, and no leaf rule ID was added,
removed, or renamed.

## 3. Version boundary

- The rule/manual artifact and four registries remain `0.3.1`.
- `RULES.json.schema_version` remains `0.3.0`.
- All 11 schemas, their IDs, byte counts, and SHA-256 values remain the
  original v0.3.0 contract.
- The Phase 2 audit remains an immutable record of v0.3.0 with SHA-256
  `6de8679ad90d88a48f6ad792ee1fcd54046c10f647c8d8a813c211db772bf48a`.

The later English-only packaging migration removed translated presentation
fields without changing these semantic or schema boundaries.

## 4. Updated assets

Phase 3 updated the documentation entry point, English manual, taxonomy,
version and decision records, benchmark README, four machine registries, and
the distillation checker. It also created this completion report.

It did not modify:

- the immutable Phase 2 adversarial audit;
- the schema manifest, schema README, or any of the 11 schemas;
- the three synthetic smoke manifests and four Lean fixtures;
- formal task directories or held-out custody;
- evidence indexes, example records, or counterexample materials;
- the pinned environment manifest or unrelated EFG work.

## 5. Checker improvements

The structural checker additionally enforced the artifact/schema dual-version
boundary, frozen 75-ID order and aliases, all 13 revised metadata and wording
anchors, manual-to-registry synchronization, real Unicode and checker
contracts, complete pinned source paths/blobs, immutable Phase 2 and smoke
asset hashes, schema integrity, and the absence of generated `.olean` or
`.ilean` files under the benchmark tree.

The English-only packaging migration later replaced the former dual-language
manual comparison with an English-only distribution scan.

## 6. Validation record

The following commands passed from the repository root on 2026-08-13:

```bash
python3 benchmarks/mathlib-style/scripts/check_distillation.py
python3 benchmarks/mathlib-style/scripts/check_benchmark.py
git diff --check
git status --short --branch
```

The checks confirmed 75 rules, 10 evidence anchors, three smoke cases and four
Lean files, 14 fixed machine sources, 11 frozen schemas, 14 immutable Phase 2/
case/fixture/held-out files, matching local Mathlib commit and source blobs,
valid JSON/JSONL, no generated Lean artifacts, and no whitespace errors.

## 7. Phase 4 handoff

At the Phase 3 boundary, Phase 4 still needed source mining for 16 real,
traceable pilot cases; physical public/private separation; two independent
annotations and adjudication; the complete linter, warning, axiom-delta,
preservation, and scoring harness; two-environment validation; leakage checks;
and held-out evaluation.

The three `SYNTHETIC_SMOKE` cases only exercised layout, metadata, the static
guard, and basic compilation. They could not support benchmark-completion or
model-capability claims.

## 8. Git boundary

The original Phase 3 work did not stage, commit, push, clean, or rewrite
unrelated EFG worktree changes. This report records the historical phase
boundary; current repository status is tracked separately.
