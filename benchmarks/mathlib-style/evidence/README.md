# Evidence indexes

[`RULES.json`](../manifests/RULES.json) contains the complete 75-leaf-rule
catalog. [`SOURCES.json`](../manifests/SOURCES.json) pins contributor prose,
Mathlib code, and linter sources; [`VALIDATORS.json`](../manifests/VALIDATORS.json)
and [`COVERAGE.json`](../manifests/COVERAGE.json) retain validator and coverage
registries.

The six retrieval indexes preserve the five legacy category groups while
splitting the mixed declarations group by its primary content:

- `naming/`: `NAM-*`;
- `statements/`: `FMT-*` and `STM-*`;
- `api/`: `API-*`;
- `proofs/`: `PRF-*`;
- `documentation/`: `DOC-*`;
- `imports/`: `FIL-*` and `LOC-*`.

Together their indexes partition all 75 leaf IDs exactly. The two old mixed
declaration anchors remain single records: `DEC-E001` is routed to statements,
and `DEC-E002` to API according to its primary content. This preserves 10
unique evidence IDs rather than duplicating an anchor across directories.

Each `EXAMPLES.jsonl` record retains its pinned commit, repository-relative
source path, Git blob SHA, line range, anchor, leaf-rule links, assessment, and
explanation. Examples support contextual judgments but do not turn a heuristic
into a universal rule or override direct policy and pinned validator behavior.

`counterexamples/` is reserved for classified Phase 2 evidence, and `audits/`
contains only the not-started adversarial-audit target in this phase.
