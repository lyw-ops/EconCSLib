# Mathlib Style Distillation Decisions

This log records repository-level choices that are easy to lose when the
manual, evidence, and benchmark evolve independently. The English manual is
normative; this file explains packaging and evaluation decisions.

## D001 — Independent version snapshots

**Decision:** Keep three identities separate:

- evaluation environment: Mathlib `v4.30.0`, commit
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`, Lean
  `leanprover/lean4:v4.30.0`;
- contributor-policy snapshot: `MATHLIB-POLICY-2026-08-13`, commit
  `7b967eb1aaab674bd6aead708d42c4a83e2aca05` of the community site;
- historical source environment: recorded per mined benchmark case.

**Reason:** Mathlib releases do not version the contributor prose, and old PRs
may require a different compiler context. Combining the three makes evidence
non-reproducible.

## D002 — English is normative

**Decision:** `MANUAL_EN.md` is the specification. The Chinese
manual explains it but cannot override it.

**Reason:** One normative text prevents bilingual wording drift from creating
two incompatible gold standards.

## D003 — Leaf rules are the annotation unit

**Decision:** Preserve the v0.3.0 catalog of 75 leaf rules in
`../../../benchmarks/mathlib-style/manifests/RULES.json`. New findings must use leaf IDs; legacy aliases remain
lookup aids only.

**Reason:** Mixed rules cannot be scored or adjudicated reliably when only one
part of the rule applies.

## D004 — Rule strength and finding priority are separate

**Decision:** Rules have `MUST`, `SHOULD`, `PREFER`, or `CONTEXT` strength.
Each concrete finding independently has `BLOCKING`, `SUBSTANTIVE`, `MINOR`, or
`INFORMATIONAL` priority.

**Reason:** A general default may be minor in one patch and release-blocking in
another. Encoding priority in the rule catalog loses case context.

## D005 — Evidence is partitioned for retrieval, not authority

**Decision:** Map every leaf rule into exactly one retrieval directory:

| Directory | Rule families |
|---|---|
| `naming/` | `NAM-*` |
| `statements/` | `FMT-*`, `STM-*` |
| `api/` | `API-*` |
| `proofs/` | `PRF-*` |
| `documentation/` | `DOC-*` |
| `imports/` | `FIL-*`, `LOC-*` |

The six indexes remain an exact partition of the same five legacy category
groups; the old declarations group is split into statement/formatting and API
retrieval views. `RULES.json`, `SOURCES.json`, `VALIDATORS.json`, and
`COVERAGE.json` remain the
canonical machine-readable records. Category indexes and example anchors may
be regenerated from them.

**Reason:** The five-directory layout is convenient for retrieval, while the
single catalog prevents duplicated rule cards from diverging.

## D006 — Benchmark directories are datasets, task is metadata

**Decision:** Formal cases are organized by task as `cases/pair/`,
`cases/detect/`, `cases/repair/`, and `cases/locate/`. The existing synthetic
development data remains visibly labeled under `fixtures/positive/`,
`fixtures/negative/`, and `fixtures/repair/`; held-out custody is separate.
A case's task remains explicit metadata (`PAIR`, `DETECT`, `REPAIR`, or
`LOCATE`) rather than being inferred solely from its directory.

**Reason:** Positive/negative/repair remains useful for public smoke fixtures,
but it would reveal labels if used as the primary formal-case layout. Task type
controls prediction schema and scoring without making pair and location cases
awkward.

## D007 — Compilation is necessary but insufficient

**Decision:** Final benchmark acceptance requires compilation, no
`sorry`/`admit`, no candidate-introduced `axiom`/`constant`, empty target axiom
delta, warning allow-list compliance, pinned validators, and machine-checked
statement/specification preservation where claimed.

**Reason:** Lean can compile semantically weakened or stylistically invalid
repairs, and trusted declarations can conceal missing proofs.

## D008 — Held-out custody is physical

**Decision:** Commit only the held-out policy README. Do not commit held-out
gold or answer-revealing provenance. Public prompts and private evaluation
artifacts must be stored under separate custody for a real release.

**Reason:** Prompt wording alone cannot prevent accidental leakage through
adjacent metadata or version control history.

## D009 — Phase 3 benchmark maturity at handoff

**Decision:** At the Phase 3 handoff, the included cases were labeled
`SYNTHETIC_SMOKE`. They verify
layout, metadata, placeholder checks, and basic compilation. They are not the
planned 16 real traceable pilot cases.

**Open work:** implement full linter execution, warning extraction and
allow-lists, axiom-delta collection, statement-preservation checks, task
scoring, physical public/private datasets, source mining, two independent
annotations, and adjudication. The frozen public/private schema definitions are
present; the corresponding formal pilot data is not.

**Phase 4 note:** D013 records the later pilot implementation without rewriting
this historical handoff decision.

## D011 — Schema recovery and integrity

**Decision:** The complete set of 11 v0.3.0 JSON Schemas is copied verbatim
from the supplied `mathlib_style_v0.3.0 3` artifact. A local schema manifest
preserves the original byte counts and SHA-256 values, and repository checks
enforce the exact file set, Draft 2020-12 declarations, unique IDs, keyword
shape, and local-reference resolution.

**Reason:** The source artifact and its manifest provide stronger provenance
than reconstructing or normalizing the schema documents. Keeping the bytes
unchanged preserves the frozen contract.

## D010 — Migration provenance

**Decision:** The manuals and machine registries were migrated without changing
their v0.3.0 substantive rule content from the supplied
`mathlib_style_v0.3.0 3` input artifact. Filenames were made unversioned at the
stable paths requested here; internal `version` fields remain `0.3.0`.

**Reason:** Stable paths are easier for agents to consume, while explicit
metadata preserves the source artifact version.

## D012 — Phase 3 is a v0.3.1 normative patch, not a schema migration

**Decision:** Resolve all 13 P1/P2 findings from the immutable Phase 2 audit by
releasing the rule/manual artifact and machine registries as `v0.3.1`. Preserve
all 75 leaf rule IDs, legacy aliases, and task definitions. Keep the complete
11-file benchmark data schema set byte-for-byte at `v0.3.0`, and do not create
formal, training, test, or held-out cases in this phase.

The revision narrows claims to the pinned implementations: uncommon import
modifiers do not receive an invented total order; `Lake.*` remains a reviewable
header warning rather than an unconditional prohibition; empty-line and option
checks expose their exact scopes; Unicode uses the real
`linter.unicodeLinter`; docstring mechanics are separated from prose and link
resolution; native-decision validation combines the syntax linter with the
actual `leanchecker` gate; and the two import-minimization tools retain their
opposite local scan directions. `DOC-002C` keeps `SHOULD` with explicit limited
exceptions, while `API-007` becomes `SHOULD` for ordinary applicable cases with
documented transformation exceptions.

**Reason:** These are backward-compatible corrections to normative wording and
validator/source metadata, not changes to benchmark record shape. A patch
version makes the repaired artifact distinguishable without pretending that a
new case schema or completed benchmark exists.

## D013 — Phase 4 pilot identity and release boundary

**Decision:** Version the 16-case formal pilot independently as
`MATHLIB-STYLE-PILOT-0.1.0`. Keep public prompts in the task directories and
all answer-revealing gold, provenance, randomized canonical mappings,
annotations, adjudication, executable reference repairs, validation records,
and logs under Git-ignored `heldout/private/` custody. Six PAIR mirrors verify
A/B consistency but do not increase the primary count.

Two independent blind annotations were produced by isolated AI agents and only
then adjudicated. They are not human annotations. The pilot passes the pinned
local hard gates and deterministic scorer; local environment evidence records
the identity, command, exit code, duration, and log hashes, while the Linux
workflow is configured to upload the same evidence shape. It nevertheless remains
`linux-validation-pending` and `human-review-pending`; creating a workflow is
not evidence of an actual Linux run.

**Reason:** A separate pilot identity prevents dataset maturity from changing
the frozen `v0.3.1` rule/manual or `v0.3.0` schema identities. Physical custody
and explicit pending states prevent answer leakage and premature release
claims.
