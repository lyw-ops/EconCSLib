# Mathlib Style Distillation: Architecture and Repository Integration

- **Status date:** 2026-08-13
- **Phase 1:** Complete
- **Artifact version at integration:** `v0.3.0`
- **Benchmark maturity:** Incomplete and unpublished
- **Document role:** Architecture, status, and scope; not a style specification

## 1. Outcome

Mathlib Style Distillation Phase 1 integrated the official assets into:

- `docs/research/mathlib-style/`;
- `benchmarks/mathlib-style/`.

The migration preserved 75 unique leaf rule IDs, four rule-strength levels,
four finding priorities, four benchmark task types, four machine registries,
10 pinned evidence anchors, three synthetic smoke fixtures, public/private
custody boundaries, environment and provenance pins, and all 11 v0.3.0 JSON
Schemas.

The legacy root directory was removed only after migration comparison, static
validation, and pinned-environment smoke compilation passed. Phase 1
completion did not imply benchmark completion.

## 2. Architecture decision

Repository integration is preferable to a separate root package:

1. the root `AGENTS.md` contains only a short entry point;
2. human-readable specifications live under `docs/research/mathlib-style/`;
3. benchmark behavior, evidence, cases, fixtures, manifests, and scripts live
   under `benchmarks/mathlib-style/`;
4. `MANUAL_EN.md`, `TAXONOMY.md`, and `RULES.json` have separate roles;
5. Evaluation Mode and Distillation/Audit Mode are distinct;
6. visible fixtures and formal cases are distinct;
7. formal cases are organized by task rather than answer-revealing
   positive/negative directories.

Rule strength, finding priority, evidence class, and counterexample
classification remain independent dimensions.

## 3. Authority modes

### Evaluation Mode

`MANUAL_EN.md` is the sole normative specification. `TAXONOMY.md` is a
human-readable index, while `RULES.json` defines machine-readable rule
identity.

Compilation proves only basic Lean acceptability. It does not by itself prove
logical correctness, mathematical fidelity, API quality, Mathlib-style
conformity, or maintainability.

### Distillation/Audit Mode

Audits must use the pinned Mathlib v4.30.0 source tree, the independently
pinned contributor-policy snapshot, and pinned validator behavior. The manual
cannot prove its own correctness.

Observed exceptions are classified independently as genuine counterexamples,
legitimate exceptions, domain-specific patterns, compatibility constraints,
generated code, legacy code, or inconclusive evidence.

## 4. Asset layout

The documentation directory contains the normative manual, exact 75-rule
taxonomy, decisions, version identities, and status reports.

The benchmark directory contains:

- benchmark-specific agent instructions and README;
- six evidence retrieval indexes;
- counterexample policy and the adversarial-audit record;
- four formal task directories;
- three classes of visible smoke fixtures;
- held-out custody policy;
- registries, an environment manifest, and schemas;
- static, structural, compilation, and later Phase 4 validation tools.

The six evidence indexes partition the rules as follows:

| Retrieval index | Rule families | Count |
|---|---|---:|
| naming | `NAM-*` | 12 |
| statements | `FMT-*`, `STM-*` | 24 |
| api | `API-*` | 7 |
| proofs | `PRF-*` | 7 |
| documentation | `DOC-*` | 13 |
| imports | `FIL-*`, `LOC-*` | 12 |
| **Total** | all leaf rules | **75** |

These indexes support retrieval; they do not create another normative
authority.

## 5. Schema recovery

The complete v0.3.0 schema set was recovered from the supplied
`mathlib_style_v0.3.0 3` artifact rather than reconstructed. The 11 Draft
2020-12 files are:

1. `annotation.schema.json`;
2. `common.schema.json`;
3. `detect-case.schema.json`;
4. `locate-case.schema.json`;
5. `pair-case.schema.json`;
6. `prediction.schema.json`;
7. `private-gold.schema.json`;
8. `private-provenance.schema.json`;
9. `public-case.schema.json`;
10. `repair-case.schema.json`;
11. `validation-record.schema.json`.

They were copied byte-for-byte. The local manifest retains the original byte
counts and SHA-256 values. Checks verify the exact file set, hashes, Draft
version, unique schema IDs, keyword shapes, and all local `$ref` and JSON
Pointer resolutions. Standard `jsonschema` validation also checked the schemas
and the 12 source examples.

## 6. Independent version identities

The evaluation environment is Mathlib `v4.30.0` at commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f` with Lean
`leanprover/lean4:v4.30.0` and environment ID `MATHLIB-4.30.0`.

The policy snapshot is `MATHLIB-POLICY-2026-08-13` at community-site commit
`7b967eb1aaab674bd6aead708d42c4a83e2aca05`.

Historical cases carry their own source environments. These three identities
must not be conflated.

## 7. Validation and scope

Run from the repository root:

```bash
python3 benchmarks/mathlib-style/scripts/check_distillation.py
python3 benchmarks/mathlib-style/scripts/check_benchmark.py
git diff --check
```

The checks cover layout, rule identity, manual/taxonomy synchronization,
registry references, evidence partitioning, Markdown links, frozen schemas,
evidence anchors, fixture metadata, custody rules, forbidden constructs,
pinned checkout identity, compilation, and unexpected warnings.

The original smoke harness was not a full benchmark harness: it did not yet
perform every style linter, axiom delta, case warning allow-list,
statement/specification-preservation, or task-scoring gate.

The integration work did not modify, format, stage, commit, or clean unrelated
EFG files. Later benchmark phases are documented separately.

## 8. English-only packaging note

On 2026-08-14, this report moved to an English, language-neutral path. The
packaging migration did not change the architecture decision, rule semantics,
or version identities.
