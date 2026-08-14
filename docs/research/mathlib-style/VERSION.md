# Mathlib Style Artifact Version

- **Status date:** 2026-08-13
- **Rule/manual artifact version:** `v0.3.1`
- **Benchmark data schema version:** `v0.3.0`
- **Pilot release identity:** `MATHLIB-STYLE-PILOT-0.1.0`
- **Asset maturity:** `phase3-normative-revision-complete`
- **Benchmark maturity:** `linux-validation-pending`; `human-review-pending`;
  not a completed or published benchmark
- **Distribution language:** English only

## Evaluation environment

- Mathlib release: `v4.30.0`
- Mathlib commit: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- Lean toolchain: `leanprover/lean4:v4.30.0`
- Environment ID: `MATHLIB-4.30.0`

This identity controls compiler, linter, import-tool, and smoke-fixture
behavior. See
[`mathlib-4.30.md`](../../../benchmarks/mathlib-style/manifests/mathlib-4.30.md)
and [`SOURCES.json`](../../../benchmarks/mathlib-style/manifests/SOURCES.json).

## Policy snapshot

- Snapshot ID: `MATHLIB-POLICY-2026-08-13`
- Repository: `leanprover-community/leanprover-community.github.io`
- Commit: `7b967eb1aaab674bd6aead708d42c4a83e2aca05`

The contributor-policy snapshot is independently versioned from Mathlib code.

## Historical case source environments

The Phase 4 pilot contains 14 `NATURAL_PR` primary cases and 2
`OFFICIAL_GUIDE_EXAMPLE` primary cases. Each private provenance record carries
its source repository, review reference, base/merge or source revision,
toolchain, license, porting changes, grouping keys, and before/after hashes.
Those per-case identities are private custody metadata and are not conflated
with either the evaluation environment or policy snapshot. The three original
synthetic smoke fixtures remain development fixtures and are not pilot cases.

## Frozen schema contract

All 11 `v0.3.0` JSON Schemas were recovered from the supplied
`mathlib_style_v0.3.0 3` artifact, copied verbatim, and verified against the
byte counts and SHA-256 values in its `MANIFEST_v0.3.0.json`; no schema fields
or semantics were guessed. Phase 3 does not migrate or weaken that data
contract: schema files, schema IDs, schema versions, fixtures, formal-case
placeholders, and held-out custody remain unchanged.

## Phase 3 status

Phase 3 is **complete** for the normative artifact. Version `v0.3.1` resolves
all 13 P1/P2 findings in the immutable Phase 2 audit of `v0.3.0`. The patch
changes rule wording, selected rule strength/automation metadata, validator
descriptions, and pinned source coverage while preserving all 75 leaf rule IDs,
legacy aliases, and the `PAIR` / `DETECT` / `REPAIR` / `LOCATE` task union.

The Phase 2 audit remains an immutable record of its `v0.3.0` target. It is not
rewritten to describe the revised artifact. The detailed disposition and
validation record is in
[`PHASE3_COMPLETION_REPORT.md`](PHASE3_COMPLETION_REPORT.md).

The later English-only packaging migration removed translated presentation
fields and moved status reports to language-neutral English paths. It did not
change the normative English rule text, rule identities, or version pins.

## Phase 4 pilot status

`MATHLIB-STYLE-PILOT-0.1.0` contains exactly 16 primary cases (PAIR 6, DETECT
4, REPAIR 3, LOCATE 3) and 6 separately counted PAIR mirrors. Public prompts
and ignored private custody are physically separated. Local schema,
compilation, forbidden-construct, axiom, warning, validator, preservation,
hash, recursive leakage, provenance, annotation-isolation, mirror, executable
REPAIR, and scoring gates pass in a recorded local environment run; two
independent AI-agent blind annotations and adjudication are present.

The pilot is not complete under the Phase 4 release rule because an actual
pinned Linux run has not occurred and the agent annotations have not received
human review. The precise statuses are `linux-validation-pending` and
`human-review-pending`. This does not affect completion of the Phase 3
normative revision.
