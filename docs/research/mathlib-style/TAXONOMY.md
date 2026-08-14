# Mathlib Style Rule Taxonomy

This is the human-readable index generated from
[`RULES.json`](../../../benchmarks/mathlib-style/manifests/RULES.json) version
`0.3.1`. `RULES.json` is the machine-readable source of rule identity. This
document does not add, remove, rename, or redefine a rule. The rule/manual
artifact is `0.3.1`; the benchmark data schemas remain frozen at `0.3.0`.

## Independent dimensions

The data model keeps four judgments separate:

1. **Rule strength:** `MUST`, `SHOULD`, `PREFER`, or `CONTEXT` describes the
   general force of a rule.
2. **Finding priority:** `BLOCKING`, `SUBSTANTIVE`, `MINOR`, or
   `INFORMATIONAL` describes one finding in one case, not the rule itself.
3. **Evidence class:** `DIRECT_MANUAL`, `REVIEW_HEURISTIC`,
   `SYNTHESIZED_GUIDANCE`, or `BENCHMARK_POLICY` records the kind of support.
4. **Counterexample classification:** `GENUINE_COUNTEREXAMPLE`,
   `LEGITIMATE_EXCEPTION`, `DOMAIN_SPECIFIC`, `COMPATIBILITY_CONSTRAINT`,
   `GENERATED_CODE`, `LEGACY_CODE`, or `INCONCLUSIVE` classifies an observed
   exception independently of the preceding three dimensions.

The counterexample classification list is retained as a Phase 2 requirement;
it is not added to the frozen machine schema during this migration. Automation
(`DETERMINISTIC`, `ASSISTED`, or `HUMAN`) is a further operational property,
not a replacement for any of these dimensions.

The benchmark task union remains `PAIR`, `DETECT`, `REPAIR`, and `LOCATE`.

## Naming — 12 rules

| Rule ID | Title | Strength | Evidence | Automation |
|---|---|---|---|---|
| `NAM-001` | Semantic capitalization | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `NAM-002` | Function names follow return type | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `NAM-003` | Fields and constructors | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `NAM-004` | American spelling | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `NAM-005` | Conclusion-first theorem names | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `NAM-006` | Hypotheses after of | `PREFER` | `DIRECT_MANUAL` | `HUMAN` |
| `NAM-007` | Standard vocabulary | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `NAM-008` | Namespaces and dot notation | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `NAM-009` | Coercion names | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `NAM-010A` | Extensionality names | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `NAM-010B` | Injectivity names | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `NAM-010C` | Induction and recursor names | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |

## Formatting, statements, and API — 31 rules

| Rule ID | Title | Strength | Evidence | Automation |
|---|---|---|---|---|
| `FMT-001` | Line length | `SHOULD` | `DIRECT_MANUAL` | `DETERMINISTIC` |
| `FMT-002` | Spaces around operators | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `FMT-003` | Indentation | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `FMT-004` | Placement of by and calc | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `FMT-005` | Explicit declaration types | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `FMT-006` | Binder formatting | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `FMT-007` | Anonymous functions | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` |
| `FMT-008` | Application syntax | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` |
| `FMT-009` | Goal focusing | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `FMT-010` | One tactic per line | `PREFER` | `DIRECT_MANUAL` | `HUMAN` |
| `FMT-011` | No blank lines inside declarations | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `FMT-012` | Scoped production options | `MUST` | `DIRECT_MANUAL` | `ASSISTED` |
| `FMT-013` | Closed sections and namespaces | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` |
| `FMT-014` | Focusing-dot syntax | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` |
| `FMT-015` | Scoped Classical opening | `SHOULD` | `DIRECT_MANUAL` | `DETERMINISTIC` |
| `FMT-016` | Use change for goal changes | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` |
| `FMT-017` | Heartbeat changes require scope and explanation | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` |
| `FMT-018` | Use Type* for arbitrary universes | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` |
| `FMT-019` | Readable allowed Unicode | `MUST` | `DIRECT_MANUAL` | `ASSISTED` |
| `STM-001` | Hypotheses left of colon | `PREFER` | `DIRECT_MANUAL` | `HUMAN` |
| `STM-002` | Avoid conjunction hypotheses | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `STM-003` | Split conjunction conclusions | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `STM-004` | Avoid disjunction hypotheses | `PREFER` | `DIRECT_MANUAL` | `HUMAN` |
| `STM-005` | Canonical normal forms | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `API-001` | Complete usable API | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` |
| `API-002` | Propositional API over definitional accidents | `CONTEXT` | `SYNTHESIZED_GUIDANCE` | `HUMAN` |
| `API-003` | Appropriate generality | `CONTEXT` | `REVIEW_HEURISTIC` | `HUMAN` |
| `API-004` | Standard bundling patterns | `CONTEXT` | `SYNTHESIZED_GUIDANCE` | `HUMAN` |
| `API-005` | Appropriate attributes | `CONTEXT` | `REVIEW_HEURISTIC` | `HUMAN` |
| `API-006` | Instance diamond safety | `CONTEXT` | `REVIEW_HEURISTIC` | `HUMAN` |
| `API-007` | Transformation parity | `SHOULD` | `SYNTHESIZED_GUIDANCE` | `ASSISTED` |

## Proofs — 7 rules

| Rule ID | Title | Strength | Evidence | Automation |
|---|---|---|---|---|
| `PRF-001` | Reuse existing lemmas | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` |
| `PRF-002` | Decompose long proofs | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` |
| `PRF-003` | Readable tactic choice | `PREFER` | `REVIEW_HEURISTIC` | `HUMAN` |
| `PRF-004` | Stable proof structure | `CONTEXT` | `SYNTHESIZED_GUIDANCE` | `HUMAN` |
| `PRF-005` | No unused tactic steps | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` |
| `PRF-006` | Avoid deprecated Lean-3-style tactics | `SHOULD` | `DIRECT_MANUAL` | `DETERMINISTIC` |
| `PRF-007` | No native_decide in mathlib proofs | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` |

## Documentation — 13 rules

| Rule ID | Title | Strength | Evidence | Automation |
|---|---|---|---|---|
| `DOC-001A` | Module docstring presence and position | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` |
| `DOC-001B` | Module title and summary | `MUST` | `DIRECT_MANUAL` | `HUMAN` |
| `DOC-001C` | Relevant module sections | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `DOC-002A` | Definition docstrings | `MUST` | `DIRECT_MANUAL` | `ASSISTED` |
| `DOC-002B` | Major-theorem docstrings | `MUST` | `DIRECT_MANUAL` | `HUMAN` |
| `DOC-002C` | Structure and class field documentation | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `DOC-002D` | Useful lemma docstrings | `PREFER` | `DIRECT_MANUAL` | `HUMAN` |
| `DOC-003` | Mathematical meaning | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` |
| `DOC-004` | Sentence and theorem formatting | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `DOC-005` | Cross-references | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `DOC-006` | Proof sketches and comments | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` |
| `DOC-007` | Warnings and scope | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` |
| `DOC-008` | Literature references | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |

## Files and location — 12 rules

| Rule ID | Title | Strength | Evidence | Automation |
|---|---|---|---|---|
| `FIL-001` | File naming | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `FIL-002A` | Standard header syntax | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` |
| `FIL-002B` | Author attribution semantics | `CONTEXT` | `DIRECT_MANUAL` | `HUMAN` |
| `FIL-003` | Module and import order | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `FIL-005` | Import organization | `PREFER` | `DIRECT_MANUAL` | `ASSISTED` |
| `FIL-006` | Top-level alignment | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` |
| `FIL-007` | File cohesion and size | `CONTEXT` | `REVIEW_HEURISTIC` | `ASSISTED` |
| `FIL-008` | Header-level prohibited imports | `MUST` | `DIRECT_MANUAL` | `ASSISTED` |
| `LOC-001` | Correct home file | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` |
| `LOC-002A` | Import minimization | `SHOULD` | `REVIEW_HEURISTIC` | `ASSISTED` |
| `LOC-002B` | Dependency direction | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` |
| `LOC-003` | Duplicate and general-result search | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` |

## Count check

| Group | Count |
|---|---:|
| `NAM-*` | 12 |
| `FMT-*` / `STM-*` / `API-*` | 31 |
| `PRF-*` | 7 |
| `DOC-*` | 13 |
| `FIL-*` / `LOC-*` | 12 |
| **Total** | **75** |
