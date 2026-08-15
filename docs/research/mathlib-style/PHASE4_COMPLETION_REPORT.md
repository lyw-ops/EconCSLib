# Mathlib Style Benchmark Phase 4 Completion-Status Report

**Status: Linux validation passed; `human-review-pending`.**

The local 16-case pilot, isolated custody, two AI-agent blind annotations,
adjudication, hard-gate harness, deterministic scoring, and pinned Linux
validation were implemented and passed. Phase 4 is not complete under its
acceptance rule because qualified independent human review is not present.

## 1. Goal and scope

Phase 4 created the independent dataset identity
`MATHLIB-STYLE-PILOT-0.1.0`. It did not change rule/manual v0.3.1, schema
v0.3.0, Mathlib v4.30.0, Lean 4.30.0, environment `MATHLIB-4.30.0`, or policy
snapshot `MATHLIB-POLICY-2026-08-13`.

The delivery comprises 16 real primary cases, six PAIR mirrors, physically
isolated private annotations/gold/provenance/validation, executable hard gates,
deterministic scoring, and public reports.

## 2. Added or extended assets

The public Phase 4 surface includes:

- 22 public case directories under
  `cases/{pair,detect,repair,locate}/msb_*/`;
- `manifests/PILOT_CASES.json` and `manifests/PUBLIC_SHA256.json`;
- the Phase 4 harness, scorer, repair evaluator, provenance and annotation
  audits, environment runner, preservation checker, requirements, and tests;
- the public baseline inventory, runbooks, and pilot report;
- `.github/workflows/mathlib-style-phase4.yml` as the Linux entry point;
- status and index updates in the English documentation.

Private `heldout/private/` custody contains provenance, annotations,
adjudication, gold, reference repairs, validation specifications and records,
logs, scoring self-tests, and release manifests. It is Git-ignored.

## 3. Preserved identities and assets

Phase 4 preserved the English manual, taxonomy, 75 leaf IDs and order, rule
strengths, normative content, aliases, all 11 frozen v0.3.0 schemas, the
immutable Phase 2 audit, the Phase 3 report, the three synthetic smoke
fixtures, the original case-policy READMEs, and the environment and policy
pins.

The pre-Phase-4 61-file baseline is stored in
`reports/phase4/BASELINE_SHA256.json`. The preservation checker identifies the
small, explicit integration surface allowed to differ. The later English-only
packaging migration explicitly records its registry changes and removal of
redundant translated files without weakening the frozen schema or rule checks.

## 4. Safe pilot summary

- Tasks: PAIR 6, DETECT 4, REPAIR 3, LOCATE 3.
- Strata: Surface 4, Documentation/Statement 4, Proof 4,
  API/Integration 4.
- Sources: 14 `NATURAL_PR`, two `OFFICIAL_GUIDE_EXAMPLE`, zero synthetic
  primary cases.
- Evaluation modes: nine closed-context and seven repository-agent cases.
- PAIR mirrors: six, excluded from the 16-primary count.
- Private answerability summary: 13 `ANSWERABLE`, two
  `MULTIPLE_ACCEPTABLE`, one `INSUFFICIENT_CONTEXT`.

The public pilot report lists only safe case IDs, tasks, strata, and modes. It
does not expose per-case gold or provenance locators.

## 5. Source mining and provenance

Cases use the pinned Mathlib checkout, official Mathlib PR/review/commit/source
material, and the official contributor guidance. Fourteen natural cases carry
real review signals; two cases come from official guide examples. A case was
excluded if porting to v4.30.0 changed the review signal, statement, API
semantics, or answer.

All 16 private provenance records contain source repository and review
identity, base/merge or source revision, before/after material, source file and
declaration, original toolchain, license, a paraphrased review signal,
v4.30.0 differences, porting changes, endpoint SHA-256 values, and source/
module/theorem-family grouping keys.

The offline provenance audit verifies canonical PR, discussion, and merge URLs
for the 14 natural cases; preserved patch and source material; public wrapper
hashes; and pinned official source hashes for the two guide cases. Public
prompts are scanned for reverse-locatable source identifiers.

## 6. Annotation and adjudication

After the public cases and `PUBLIC_SHA256.json` were frozen, two isolated
snapshots were created. Annotators A and B were AI agents. Each could read only
the English manual, `RULES.json`, `VALIDATORS.json`, the 16 public primary
cases, and task-permitted pinned repository context. Neither could read
provenance, reference repairs, the other annotation, gold, or adjudication.

Each annotator completed 16 schema-valid annotations with 14 HIGH and two
MEDIUM confidence labels. Each isolation snapshot retained 76 allowed files
and had a distinct inventory hash. Automated checks verified timing,
inventories, all 16 outputs, and `saw_other_annotation: false`.

Adjudication began only after both annotation sets were complete. Agreement
was 15/16 for answerability, 16/16 for abstention, 14/16 for confidence, 14/16
for finding rule sets, 6/6 for PAIR verdicts, and 3/3 for LOCATE locations.
Five cases required substantive adjudication. Every primary case has a final
accepted set.

These are agent annotations, not human annotations. No validation record marks
a `human.*` validator as executed; human review remains pending.

## 7. Harness implementation

| Capability | Implementation |
|---|---|
| Schema | Standard Draft 2020-12 `jsonschema` plus an offline local-reference registry |
| Compilation | Per-case compiler and text-linter temporary trees, 90-second timeout, repeated Lean elaboration, normalized reproducibility comparison |
| Forbidden constructs | Static rejection of placeholders, candidate axioms/constants, native-decision trust escapes, and critical linter disabling |
| Axioms | Target `#print axioms` baseline, observed set, and delta; REPAIR delta is a hard gate |
| Warnings | Separate linter baseline and observed warnings with case allow-lists and hard failure on unexpected warnings |
| Validators | Standard Mathlib set, text/Unicode/header/style/native-decision checks, compiler, static guard, axiom probe, repeat elaboration, applicable location evidence, and preservation checks |
| REPAIR | Frozen wrapper reconstruction, edit contract and budget, issue resolution, compilation, linters, declaration-type preservation, axiom/warning/no-new-finding gates |
| Logs and hashes | Raw logs and SHA-256 links; separate public and private manifests |
| Leakage | Recursive public scans, strict public layout, private Git-ignore, and generated-artifact checks |
| Scoring | Task-aware deterministic metrics for 16 primary cases and separate PAIR-mirror consistency; no LLM judge |

`custom.doc_link_check` remains unimplemented and is not marked otherwise.
Location-tool output is evidence rather than a substitute for human placement
judgment. Nondeterministic API and proof judgments are recorded through agent
annotations and adjudication, not disguised as automatic validator results.

## 8. Local validation result

The complete private Darwin run used the pinned dependency overlay and Phase 4
environment runner. Supporting commands also checked annotation isolation,
provenance, executable repairs, unit tests, perfect-prediction scoring,
distillation structure, public benchmark gates, baseline preservation, diff
whitespace, and Git status.

The final full run on Darwin 25.6.0 arm64 took 1,185.966 seconds. The identity
gate and harness both exited 0. All 22 public cases passed repeated isolated
compilation. Ninety-two schema-governed private JSON documents and 22
validation records passed. Axiom deltas and unexpected warnings were empty;
2/2 applicable location probes, 3/3 executable REPAIR cases, 6/6 mirrors, and
16/16 unit tests passed. Perfect scoring reported 1.0 for macro, micro, and
each task. The public manifest contained 67 hashes and private custody 482.

No `.olean` or `.ilean` file remained under the benchmark tree, private
custody was ignored by Git, and no file was staged.

## 9. Environment status

| Environment | Identity and result |
|---|---|
| Local | Darwin 25.6.0 arm64, Lean 4.30.0, pinned Mathlib commit; actual full run exit 0 with command and log hashes in private custody |
| Linux | Ubuntu 24.04 x86_64, Lean 4.30.0, pinned Mathlib commit; public hard gates exit 0, aggregate kernel replay passed, regression reruns passed, and environment evidence uploaded |

The successful Linux record is
[GitHub Actions run 31804054807](https://github.com/lyw-ops/EconCSLib/actions/runs/31804054807),
job `94778564899`, on exact validation commit
`51e53baa0ed86545f98bf485838be1ddcd28b4a1`. It verified public manifest
SHA-256
`bccd572e26baf8ab438d6bde263b03a0e260eda0be4e3347946a60fcbf792b43`
and uploaded artifact `mathlib-style-linux-environment-evidence` (artifact ID
`9220614313`). The evidence records Linux
`6.17.0-1022-azure` x86_64, Python 3.12.3, Lean 4.30.0, Mathlib commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, the exact public hard-gate
command, exit code 0, duration, and log SHA-256 values.

The run also passed `lake env leanchecker --fresh EconCSLib`, the frozen
distillation and fixture regression rerun, all 16 deterministic scorer tests,
and generated Lean artifact and whitespace rejection. This resolves the Linux
acceptance gate for the recorded commit and frozen public hashes.

## 10. Public/private custody

Public cases and manifests contain no answerability, gold, reference repair,
canonical A/B mapping, PR/review/commit locator, adjudication, or private path.
The ignored private release manifest covers provenance, both annotation sets,
adjudication, repairs, validation, logs, environment evidence, and scoring
assets, and links back to the public manifest hash. Gold was generated only
after both annotations and adjudication were complete.

## 11. Remaining acceptance work

1. Obtain qualified human review of both agent annotations, adjudication,
   source interpretation, and gold; retain the private review record described
   by `HUMAN_REVIEW_RUNBOOK.md`.
2. Confirm that the human-review record applies to the same frozen public and
   private hashes before changing the pilot status.
3. Make a separate release decision before describing the pilot as
   public-release eligible.

Until then the correct status remains `human-review-pending`, not complete or
public-release eligible, and the pilot must not support model-capability
conclusions.
