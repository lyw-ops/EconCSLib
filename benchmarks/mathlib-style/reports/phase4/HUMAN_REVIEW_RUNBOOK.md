# Phase 4 independent human-review runbook

This is the remaining publication gate for `MATHLIB-STYLE-PILOT-0.1.0`.
Agent annotation and agent adjudication do not satisfy it. The reviewer must be
a person with practical Lean/Mathlib review experience who did not produce the
two blind agent annotations.

## Frozen inputs

Before review, record the SHA-256 of:

- `manifests/PUBLIC_SHA256.json`;
- `heldout/private/release_manifests/PRIVATE_SHA256.json`;
- both annotation-run records and all 32 annotation documents;
- both adjudication documents and all 22 Gold documents.

The reviewer may inspect private custody. Any correction invalidates the old
private manifest and requires a new full local validation run. Public prompt
changes additionally invalidate the blind-annotation freeze and require new
independent annotations.

## Per-case review

For each of the 16 primary cases, independently check and record:

1. the canonical source URL, PR/review comment or official-guide anchor, source
   file/declaration, base/merge identities, source-material hash, license, and
   review-signal paraphrase;
2. that the v4.30.0 port preserves the source statement/API semantics and the
   original review signal, with every porting change disclosed;
3. that the public prompt contains enough allowed context, contains no source
   or answer leakage, and assigns the correct task, stratum, and evaluation mode;
4. both agent annotations, their disagreements, the adjudication rationale,
   answerability, accepted set, findings, spans, priorities, and abstention;
5. for REPAIR, the edit contract, executable issue-resolution contract,
   statement/interface preservation, axiom/warning gates, and all accepted
   repairs; for LOCATE, the `#find_home` evidence where applicable and the
   separately human architectural judgment;
6. that the final Gold follows the frozen v0.3.1 manual and uses leaf rule IDs,
   not legacy aliases.

Each case must end as `APPROVED`, `CORRECTION_REQUIRED`, or `EXCLUDE`. A case
cannot be replaced merely to preserve a quota; a replacement needs real source
mining, two new blind annotations, adjudication, and all gates.

## Required private review record

Write an ignored private record under `heldout/private/human-review/` containing:

- reviewer identity or stable audit pseudonym and `reviewer_type: HUMAN`;
- start/end timestamps and qualifications;
- the two frozen manifest hashes;
- 16 per-case statuses with concise reasons and issue references;
- explicit checks for annotation independence, provenance authenticity,
  semantic preservation, Gold correctness, leakage, and repair/location gates;
- an overall `PASS` only when all 16 cases are approved;
- reviewer attestation that no benchmark author represented the review as blind
  if the reviewer saw Gold or provenance.

Do not add fields to any frozen v0.3.0 schema for this record.

## Post-review gates

After all approved corrections, run the commands in `RUNBOOK.md`, refresh the
private custody manifest last, and retain the human-review record in that
manifest. Release eligibility still also requires a successful actual Linux
environment record over the same public manifest hash.
