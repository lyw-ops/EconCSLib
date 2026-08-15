# Mathlib Style Benchmark Phase 4 Pilot Report

- **Pilot identity:** `MATHLIB-STYLE-PILOT-0.1.0`
- **Rule/manual:** `v0.3.1`
- **Data schema:** `v0.3.0`
- **Evaluation environment:** `MATHLIB-4.30.0`
- **Status:** Linux validation passed; `human-review-pending`
- **Report date:** 2026-08-13
- **Status updated:** 2026-08-15

This public report provides only aggregates that do not reveal individual
answers. Gold, source locators, canonical A/B mappings, reference repairs,
per-case validation logs, and adjudication details remain in Git-ignored
private custody.

## 1. Pilot composition

The pilot contains exactly 16 primary cases. Six PAIR mirrors test directional
consistency and do not count as primary cases.

| Task | Primary | Mirrors |
|---|---:|---:|
| PAIR | 6 | 6 |
| DETECT | 4 | 0 |
| REPAIR | 3 | 0 |
| LOCATE | 3 | 0 |
| **Total** | **16** | **6** |

| Stratum | Count |
|---|---:|
| Surface | 4 |
| Documentation / Statement | 4 |
| Proof | 4 |
| API / Integration | 4 |

The following safe index contains public fields only.

| ID | Task | Stratum | Evaluation mode |
|---|---|---|---|
| `msb_p001` | PAIR | Surface | Closed context |
| `msb_p002` | PAIR | Surface | Closed context |
| `msb_d001` | DETECT | Surface | Closed context |
| `msb_r001` | REPAIR | Surface | Closed context |
| `msb_p003` | PAIR | Documentation / Statement | Closed context |
| `msb_d002` | DETECT | Documentation / Statement | Repository agent |
| `msb_r002` | REPAIR | Documentation / Statement | Closed context |
| `msb_p004` | PAIR | Documentation / Statement | Closed context |
| `msb_p005` | PAIR | Proof | Closed context |
| `msb_d003` | DETECT | Proof | Closed context |
| `msb_r003` | REPAIR | Proof | Repository agent |
| `msb_p006` | PAIR | Proof | Repository agent |
| `msb_d004` | DETECT | API / Integration | Repository agent |
| `msb_l001` | LOCATE | API / Integration | Repository agent |
| `msb_l002` | LOCATE | API / Integration | Repository agent |
| `msb_l003` | LOCATE | API / Integration | Repository agent |

Source classes are 14 `NATURAL_PR` and two `OFFICIAL_GUIDE_EXAMPLE`, with no
synthetic primary case. The private answerability aggregate is 13
`ANSWERABLE`, two `MULTIPLE_ACCEPTABLE`, and one `INSUFFICIENT_CONTEXT`.

The pilot covers real PAIR ties, repository-agent and closed-context modes,
compilable linter-detectable problems, statement and API design, proof reuse
and structure, and import/location decisions.

## 2. Provenance and isolation

All 16 primary cases have schema-valid private provenance. Natural-PR records
include source repository, PR/review identity, base/merge or patch identity,
source declaration, original toolchain, license, a paraphrased review signal,
v4.30.0 differences, all porting changes, endpoint SHA-256 values, and source/
module/theorem-family grouping keys. Official-guide cases carry equivalent
pinned-source and porting hashes.

The offline provenance audit checked 16/16 coverage, the 14/2/0 source-class
distribution, canonical PR/comment/commit URLs, preserved patch hashes, pinned
source-material hashes, and public ported-wrapper hashes.

Public case directories contain only `public.json`, a prompt, and README.
Private custody is excluded by `heldout/.gitignore`. Separate public and
private manifests freeze their respective assets. Recursive leakage checks
reject PR URLs, review/commit locators, answerability, gold, reference repairs,
private paths, adjudication, and direct answer fields from the public surface.

## 3. Blind annotation and adjudication

After the public prompts and guidance were frozen, two isolated AI agents each
received only the v0.3.1 English manual, rule and validator registries, the 16
public primary prompts, and task-permitted pinned repository context. They did
not receive provenance, reference repairs, the other output, gold, or
adjudication.

- Annotator A: 16/16, with 14 HIGH and two MEDIUM confidence labels.
- Annotator B: 16/16, with 14 HIGH and two MEDIUM confidence labels.
- Both annotation sets pass `annotation.schema.json`.
- Each retained isolation snapshot contains 76 allowed files and has a
  distinct inventory hash.
- Automated audits found no cross-annotation visibility.
- Adjudication began only after both sets were complete; all 16 cases have a
  final decision, and five required substantive judgment.

Exact agreement was 15/16 for answerability, 16/16 for abstention, 14/16 for
confidence, 14/16 for finding rule sets, 6/6 for PAIR verdicts, and 3/3 for
LOCATE locations. The three REPAIR intentions aligned after adjudication.
These are AI-agent agreement figures, not human agreement.

## 4. Hard gates

| Gate | Local result |
|---|---|
| Draft 2020-12 schemas and local references | Passed |
| Public inventory, task/stratum balance, mirror counts | Passed |
| Per-case compiler/text-linter trees, repeated elaboration, 90-second timeout | 22/22 passed |
| Mathlib standard linter set | 22/22 passed under case policies |
| Mathlib text and Unicode linters | 22/22 passed |
| Placeholder, axiom, constant, trust-escape, and linter-disable scans | Passed |
| Target axiom baseline/observed/delta | 22/22 with empty deltas |
| Warning baseline/observed/allow-list | 22/22 with no unexpected warnings |
| Applicable location evidence | 2/2 passed; the visibility-only case makes no tool claim |
| Executable REPAIR and statement-type preservation | 3/3 passed |
| Provenance, annotation isolation, hashes, ignore, and recursive leakage | Passed; 67 public and 482 private hashes |
| PAIR mirror transformation and consistency | 6/6 passed |
| Executable perfect REPAIR fixture | 3/3 passed; reference text is diagnostic only |
| Perfect-prediction scorer self-test | 16 primary plus six mirrors; all macro/micro/task scores 1.0 |
| Scorer and static-guard unit tests | 16/16 passed |

Validation records do not claim that any `human.*` validator ran. Applicable
API, proof, and location judgments without deterministic contracts are
captured by the two annotations and adjudication rather than represented as
automatic checks.

## 5. Deterministic primary metrics

- PAIR: verdict, accepted-set accuracy, and mirror consistency; mirrors do not
  increase the primary count.
- DETECT: leaf-rule precision, recall, F1, and declaration-aware span overlap;
  priority is reported separately.
- REPAIR: compilation, issue resolution, statement/interface preservation,
  new findings, axiom and warning gates, and edit cost; exact reference-text
  equality is not the primary metric.
- LOCATE: accepted location or accepted set, abstention, and insufficient
  context.
- Global: answerability, abstention calibration, unsupported-rationale rate,
  and breakdowns by task, stratum, source class, and evaluation mode.

All primary scores are computed deterministically without an LLM judge.

## 6. Environment result and limitation

| Environment | Result | Evidence |
|---|---|---|
| Darwin 25.6.0 arm64, Lean 4.30.0, pinned Mathlib commit | Passed | Full private run exit 0 in 1,185.966 seconds, identity and log hashes, 22 validation records, 482-asset custody manifest |
| Ubuntu 24.04 x86_64, Lean 4.30.0, pinned Mathlib commit | Passed | [Run 31804054807](https://github.com/lyw-ops/EconCSLib/actions/runs/31804054807), job `94778564899`, validation commit `51e53baa0ed86545f98bf485838be1ddcd28b4a1`, public hard gates exit 0, aggregate kernel replay and regression reruns passed, evidence artifact `9220614313` uploaded |

The Linux evidence records kernel `6.17.0-1022-azure`, Python 3.12.3, Lean
4.30.0, the pinned Mathlib commit, the exact public hard-gate command, exit
code 0, duration, and log SHA-256 values. It verifies the unchanged public
manifest SHA-256
`bccd572e26baf8ab438d6bde263b03a0e260eda0be4e3347946a60fcbf792b43`.
Both annotations were produced by AI agents and have not received independent
qualified human review.

Therefore the remaining status is `human-review-pending`. The pilot must not
be marked complete, described as public-release eligible, or used for
model-capability conclusions.
