# Mathlib Style Benchmark Phase 5 Readiness Audit

- **Audit time:** 2026-08-14 12:12:23 +08:00
- **Target release identity:** `MATHLIB-STYLE-PILOT-0.1.0-RC1`
- **Status:** `blocked-by-phase4-readiness`
- **Readiness gate:** Failed
- **Gold unseal:** Did not occur
- **Evaluation agent, prediction, and scoring:** Not started

## 1. Conclusion

Phase 5 could not enter freeze, blind evaluation, scoring, difficulty
calibration, dynamic red teaming, or RC1 packaging. The blocker was not the
16-case inventory, schemas, provenance, annotation isolation, or current
Darwin public hard gates. Phase 4 explicitly remained
`linux-validation-pending` and `human-review-pending`.

Readiness requires non-pending Phase 4 status and actual passing evidence for
both local and Linux hard gates. The audit found an actual Darwin arm64
environment record, but no Linux run artifact and no independent human-review
record.

The required unprefixed preflight also failed under the default Python runtime
because `jsonschema` was unavailable. With the pinned Phase 4 dependency
overlay, the same public harness and all 16 unit tests passed. This runtime
issue does not satisfy either the Linux or human gate and should be
standardized before the next readiness attempt.

## 2. Readiness matrix

| Check | Result | Evidence |
|---|---|---|
| Phase 4 completion-status and public pilot reports exist | PASS | Both English reports are present |
| Phase 4 status is not partial, pending, or blocked | **FAIL** | Reports state `linux-validation-pending` and `human-review-pending` |
| Primary count and task distribution | PASS | 16: PAIR 6, DETECT 4, REPAIR 3, LOCATE 3 |
| Four balanced strata | PASS | Surface, Documentation/Statement, Proof, API/Integration each have four |
| No synthetic primary | PASS | 14 natural PR cases, two official-guide examples, zero synthetic |
| Public schema, layout, and hashes | PASS | 22 public cases including six mirrors, strict three-file layout, 67 hashes |
| Private schemas and custody manifest | PASS | 92 schema-governed documents and a consistent 482-file manifest |
| Source provenance | PASS | 16/16 offline provenance audit |
| Two independent annotations | PASS | Two distinct 76-file snapshots, 16 outputs each, no cross-annotation visibility |
| Adjudication, gold, and validation inventory | PASS | Two retained annotation sets, 22 gold files, and 22 validation records are structurally complete |
| Public/private leakage | PASS | Recursive leakage, layout, hash, and mirror checks passed |
| Local hard gates | PASS | Current Darwin public rerun passed 22/22 repeated compilations; retained private Darwin record is PASSED |
| Linux hard gates | **FAIL** | No actual Linux environment record, exit code, or log-hash artifact |
| Independent human review | **FAIL** | No human-review record; Phase 4 remains pending |
| Mirrors excluded from primary count | PASS | Six mirrors remain separate from 16 primary cases |
| Private custody is Git-ignored | PASS | `git check-ignore` confirms the committed held-out policy |
| No `.olean` or `.ilean` in benchmark tree | PASS | Scan returned no result |
| No Phase 3 frozen-asset drift | PASS | Distillation and preservation checks passed; 75 rules, aliases, and 11 schemas remained intact |
| Default-Python preflight runtime | **FAIL** | Default interpreter lacked `jsonschema`; pinned overlay passed |

The public manifest SHA-256 was
`bccd572e26baf8ab438d6bde263b03a0e260eda0be4e3347946a60fcbf792b43`.
This report records only safe private-custody counts and does not disclose
per-file private hashes or content.

## 3. Executed checks

The first unmodified preflight produced:

- `check_distillation.py`: passed with 75 rules, 11 frozen schemas, and matching
  frozen assets;
- `check_benchmark.py`: failed because the default Python environment lacked
  the Phase 4 `jsonschema` runtime;
- unit-test discovery: 15 tests completed and one errored for the same missing
  dependency.

With the pinned Phase 4 local dependency overlay:

- scorer and static-guard tests passed 16/16;
- Phase 4 preservation reported 54 unchanged captured files and seven expected
  integration changes at the time of the audit;
- provenance passed 16/16 with the expected 14/2/0 source distribution;
- annotation isolation passed for two distinct 76-file snapshots;
- public hard gates passed three smoke cases, four Lean fixtures, 16 primary
  cases, six mirrors, 22 repeated compilations, and 67 public hashes;
- private schema validation passed 92 documents, and the custody manifest
  covered 482 consistent files;
- no `.olean` or `.ilean` artifact remained.

These results confirm the Darwin/public state and retained local private
evidence, but cannot replace an actual Linux run or qualified human review.

## 4. Blocking conditions and release criteria

1. Run the Phase 4 gates on the pinned Linux runner against the same public
   manifest and retain OS/architecture, Lean/Mathlib identity, full command,
   exit code, and log SHA-256 evidence.
2. Complete qualified independent human review under
   `HUMAN_REVIEW_RUNBOOK.md` and retain the review record in ignored private
   custody.
3. Update Phase 4 from pending only when both evidence sets apply to unchanged
   frozen hashes.
4. Install the pinned requirements for the unprefixed Python command or make
   the dependency overlay a standardized reproducible entry point.
5. Run a new Phase 5 readiness audit. This failed audit must not be rewritten
   into a pass.

## 5. Protocol protection

Because readiness failed, the audit did not create:

- `SCORING_PROTOCOL.json`;
- Phase 5 public or private freeze manifests;
- evaluation runs, predictions, or a prediction freeze;
- scoring, difficulty, red-team results, or a release archive;
- a `pilot-0.1.0-rc1/` release directory.

The main agent did not open, print, rewrite, or unseal private gold and did not
start an evaluation or red-team agent. Phase 5 must remain
`blocked-by-phase4-readiness` until a new readiness audit actually passes.

## 6. English-only packaging note

This report moved to an English, language-neutral path after the audit. The
packaging migration did not change the audit outcome, public manifest identity,
or release blockers.
