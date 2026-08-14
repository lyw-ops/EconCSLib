# Mathlib Style and Review Distillation Manual

- **Version:** 0.3.1
- **Status:** Phase 3 normative revision complete
- **Checked:** 2026-08-13
- **Evaluation environment:** mathlib `v4.30.0` / commit `c5ea00351c28e24afc9f0f84379aa41082b1188f` / Lean `leanprover/lean4:v4.30.0`
- **Machine-readable rules:** `../../../benchmarks/mathlib-style/manifests/RULES.json`
- **Validator registry:** `../../../benchmarks/mathlib-style/manifests/VALIDATORS.json`
- **Source registry:** `../../../benchmarks/mathlib-style/manifests/SOURCES.json`

## 1. Purpose

This manual converts mathlib style, naming, documentation, PR-review guidance, and pinned linter behavior into operational review rules. It is not an official mathlib policy document and not a complete formatter. It supports human review, review-agent retrieval, model distillation, and benchmark construction.

Code behavior is pinned to `v4.30.0`. Contributor guidance is not part of a mathlib release, so it is pinned independently as `MATHLIB-POLICY-2026-08-13`. The two snapshots must not be conflated.

## 2. v0.3.1 normative patch over v0.3.0

- Phase 3 resolves all 13 P1/P2 findings from the immutable v0.3.0 manual
  adversarial audit. It changes rule wording and validator/source metadata, not
  the benchmark data schema.
- The rule/manual artifact version is `0.3.1`; `schema_version` and all 11 JSON
  Schemas remain byte-for-byte frozen at `0.3.0`.
- The 75 leaf rule IDs, legacy aliases, and `PAIR` / `DETECT` / `REPAIR` /
  `LOCATE` task definitions remain unchanged.
- The evaluation environment remains mathlib `v4.30.0`, commit
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`, toolchain
  `leanprover/lean4:v4.30.0`; the policy snapshot remains
  `MATHLIB-POLICY-2026-08-13` at commit
  `7b967eb1aaab674bd6aead708d42c4a83e2aca05`.
- Unicode validation now cites the pinned `linter.unicodeLinter` implementation
  and allow-list. Native-decision hard validation pairs the syntax linter with
  the actual pinned `leanchecker` gate.
- Phase 3 produces no formal benchmark cases, training data, test data, or
  held-out data. Benchmark production and independent annotation remain Phase 4.

## 3. Three independent snapshots

| Snapshot | Purpose | Pinning |
|---|---|---|
| evaluation environment | compiler, linter, and import-tool behavior | mathlib `v4.30.0` + commit + toolchain |
| policy snapshot | style, naming, documentation, and review prose | contributor-site commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05` |
| source environment | original context of a historical PR | per-case base/merge commit and toolchain |

## 4. Interpretation framework

### 4.1 Rule strength

- `MUST`: explicitly required/disallowed, or decided by a pinned validator within a stated scope.
- `SHOULD`: default expectation; deviations require a concrete reason.
- `PREFER`: community preference with several acceptable alternatives.
- `CONTEXT`: depends on mathematical, architectural, or downstream-use context.

### 4.2 Automation level

- `DETERMINISTIC`: a pinned validator decides the operational condition within its documented scope.
- `ASSISTED`: machine evidence is useful, but human judgment remains necessary.
- `HUMAN`: no reliable automatic decision procedure is claimed.

### 4.3 Review priority

`BLOCKING / SUBSTANTIVE / MINOR / INFORMATIONAL` belongs to each finding, not to the rule catalog. The same `SHOULD` rule may have different review priorities in different cases.

## 5. Core rule catalog

This version contains **75 leaf rules**. `FIL-002`, `FIL-004`, `DOC-001`, `DOC-002`, `NAM-010`, and `LOC-002` are retained only as legacy aliases.

| Rule ID | Title | Strength | Evidence | Automation | Operational rule | Validator |
|---|---|---|---|---|---|---|
| `FIL-001` | File naming | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Lean source files should generally use UpperCamelCase names. Rare lower-case exceptions require prior discussion, and the file name should identify its mathematical topic. | `custom.file_name_upper_camel`, `human.file_topic_fit` |
| `FIL-002A` | Standard header syntax | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | Start a mathlib file with the standard copyright, Apache-2.0 license, and `Authors:` header syntax. | `linter.style.header` |
| `FIL-002B` | Author attribution semantics | `CONTEXT` | `DIRECT_MANUAL` | `HUMAN` | The `Authors:` list should identify substantial design/development contributors whom maintainers would contact about the file; syntax alone does not decide attribution. | `human.authorship_attribution` |
| `FIL-003` | Module and import order | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Put `module` on its own line after the header. For ordinary `public import` and `import` blocks, keep one import per line, place the public block first, and try to sort within each block; no official total order is asserted for uncommon modifiers such as `public meta import` or `import all`. | `linter.style.header`, `custom.module_import_order` |
| `FIL-005` | Import organization | `PREFER` | `DIRECT_MANUAL` | `ASSISTED` | Keep one import per line, preserve the public/ordinary grouping, prefer alphabetical order within groups, and remove imports shown to be redundant or unnecessary. | `custom.module_import_order`, `command.#min_imports_in`, `command.#redundant_imports`, `human.location_review` |
| `FIL-006` | Top-level alignment | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Keep top-level declarations and commands flush-left; do not indent the contents of namespaces or sections. | `linter.style.whitespace` |
| `FIL-007` | File cohesion and size | `CONTEXT` | `REVIEW_HEURISTIC` | `ASSISTED` | Split files according to mathematical cohesion and dependency boundaries. Roughly 1000 lines is a reviewer signal to reconsider the split; mathlib’s `longFile` linter warns above 1500 lines, while downstream projects have no long-file limit unless configured. | `linter.style.longFile`, `human.location_review` |
| `FIL-008` | Header-level prohibited imports | `MUST` | `DIRECT_MANUAL` | `ASSISTED` | Do not introduce `Mathlib.Tactic` bucket imports or other imports explicitly prohibited by the pinned header linter. `Lake.*` instead triggers a warning and may remain only after necessity review, performance benchmarking, and a justified linter allowance. | `linter.style.header`, `human.location_review` |
| `FMT-001` | Line length | `SHOULD` | `DIRECT_MANUAL` | `DETERMINISTIC` | Keep lines at or below 100 characters; the current linter permits documented exceptions such as lines containing URLs. | `linter.style.longLine` |
| `FMT-002` | Spaces around operators | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Use spaces around :, :=, and infix operators; keep an operator at the end of the preceding line when breaking. | `linter.style.whitespace`, `human.layout_review` |
| `FMT-003` | Indentation | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Use two-space continuation indentation in general, four spaces for continued theorem statements, and two spaces for proof bodies. | `human.layout_review` |
| `FMT-004` | Placement of by and calc | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Place by and calc on the line immediately preceding the proof or calculation, not on a line by themselves. | `human.layout_review` |
| `FMT-005` | Explicit declaration types | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | In public signatures, give explicit types for parameters and return values when omission would obscure readability or API meaning. Types clear from a typed dependent context—such as inferable index, universe, or similar binders `{n}` and `{m}`—may be omitted. | `human.statement_review` |
| `FMT-006` | Binder formatting | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Put a space after binders and normally state binder types explicitly. | `linter.style.whitespace`, `human.layout_review` |
| `FMT-007` | Anonymous functions | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | Use `fun`, not `λ`, for anonymous functions. The `↦` arrow is only a slight source-code preference, not a hard requirement. | `linter.style.lambdaSyntax` |
| `FMT-008` | Application syntax | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | Do not use `$` for function application in mathlib source; use `<|` instead. | `linter.style.dollarSyntax` |
| `FMT-009` | Goal focusing | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Normally focus proof goals explicitly, often with `·`, so a tactic does not unintentionally act on several goals; use documented multi-goal combinators only when intentional. | `linter.style.multiGoal`, `human.proof_review` |
| `FMT-010` | One tactic per line | `PREFER` | `DIRECT_MANUAL` | `HUMAN` | Normally place one tactic per line; compress short steps only when this clearly improves readability. | `human.proof_review` |
| `FMT-011` | No blank lines inside declarations | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Within the pinned `linter.style.emptyLine` scope, do not use blank lines to segment a command; use comments to explain proof structure. Its deterministic scope excludes doc/module docs, mutual commands, string syntax, `where` fields, incomplete commands, and paths containing `Tactic`, `Util`, or `Meta`; outside that scope the same readability question is assisted review. | `linter.style.emptyLine`, `human.layout_review` |
| `FMT-012` | Scoped production options | `MUST` | `DIRECT_MANUAL` | `ASSISTED` | Remove development options rooted at `debug`, `pp`, `profiler`, or `trace`. The pinned linter also rejects unscoped options containing `maxHeartbeats` and unscoped `linter.flexible`, deprecates `linter.style.commandStart`, and rejects new `backward.inferInstanceAs.wrap.reuseSubInstances` debt. Other technically necessary production options are not automatic failures, but must be scoped as narrowly as possible and explained when required. | `linter.style.setOption`, `human.layout_review` |
| `FMT-013` | Closed sections and namespaces | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | Close sections and namespaces before end-of-file, except for the documented outermost public/meta/noncomputable section exceptions. | `linter.style.missingEnd` |
| `FMT-014` | Focusing-dot syntax | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | Use the `·` focusing character rather than a plain dot, and do not isolate the focusing dot on a line by itself. | `linter.style.cdot` |
| `FMT-015` | Scoped Classical opening | `SHOULD` | `DIRECT_MANUAL` | `DETERMINISTIC` | Do not use file-wide `open Classical`/`open scoped Classical` when a declaration-local scope suffices. | `linter.style.openClassical` |
| `FMT-016` | Use change for goal changes | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | When a `show` command changes the goal rather than merely presenting it, use `change` as required by the pinned style linter. | `linter.style.show` |
| `FMT-017` | Heartbeat changes require scope and explanation | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | A `maxHeartbeats`-family option must be scoped to a command and accompanied by a comment explaining why the increase is necessary. | `linter.style.setOption`, `linter.style.maxHeartbeats` |
| `FMT-018` | Use Type* for arbitrary universes | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | Use `Type*` rather than `Type _` when the intention is an arbitrary universe level, unless a concrete metavariable behavior is required and justified. | `human.statement_review` |
| `FMT-019` | Readable allowed Unicode | `MUST` | `DIRECT_MANUAL` | `ASSISTED` | Reject characters and variant-selector uses disallowed by the pinned `linter.unicodeLinter`; its allow-list is snapshot-specific and may change with Mathlib. Separately, whether an allowed Unicode character improves mathematical readability is human review. | `linter.unicodeLinter`, `human.layout_review` |
| `NAM-001` | Semantic capitalization | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Use snake_case for propositions and theorems, UpperCamelCase for types in Prop/Type/Sort, and usually lowerCamelCase for other Type-valued terms. | `linter.style.nameCheck`, `environment_linter.defsWithUnderscore`, `human.naming_review` |
| `NAM-002` | Function names follow return type | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Choose a function's capitalization from the semantic category of its return type, not merely from the fact that it is a function. | `human.naming_review` |
| `NAM-003` | Fields and constructors | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Apply the same semantic naming rules to structure fields and constructors as to ordinary declarations. | `human.naming_review` |
| `NAM-004` | American spelling | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Use American English spelling in declaration names; documentation prose may use any common English spelling. | `human.naming_review` |
| `NAM-005` | Conclusion-first theorem names | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Name a theorem primarily after its conclusion rather than its proof method or a full restatement of its hypotheses. | `human.naming_review` |
| `NAM-006` | Hypotheses after of | `PREFER` | `DIRECT_MANUAL` | `HUMAN` | When hypotheses must appear in a theorem name, place them after _of_ in statement order. | `human.naming_review` |
| `NAM-007` | Standard vocabulary | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Reuse mathlib's standard symbol vocabulary, such as mul, add, one, zero, le, and lt, instead of inventing synonymous abbreviations. | `human.naming_review` |
| `NAM-008` | Namespaces and dot notation | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Place declarations in the natural namespace and support useful dot notation when they belong to a type or object; avoid repeating context in long names. | `human.naming_review` |
| `NAM-009` | Coercion names | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Name coercion declarations after their underlying function rather than hiding semantics behind a generic coe name. | `human.naming_review` |
| `NAM-010A` | Extensionality names | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Use established extensionality names such as `.ext` and `.ext_iff`, together with appropriate attributes when justified. | `human.naming_review`, `human.api_review` |
| `NAM-010B` | Injectivity names | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Follow established injectivity naming patterns such as `f_injective` and `f_inj` according to the theorem shape. | `human.naming_review` |
| `NAM-010C` | Induction and recursor names | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Respect the established distinction and parameter-order conventions for induction principles and recursors. | `human.naming_review` |
| `DOC-001A` | Module docstring presence and position | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | Except for the documented import-only and initialization exceptions, the first non-import command must be a module docstring. | `linter.style.header` |
| `DOC-001B` | Module title and summary | `MUST` | `DIRECT_MANUAL` | `HUMAN` | A module docstring must contain a first-level title and a useful summary of the file’s mathematical contents. | `human.documentation_review` |
| `DOC-001C` | Relevant module sections | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Use conventional module-docstring sections in their documented order when relevant. `Main definitions` and `Main statements` are optional; `Notation`, `References`, and `Tags` are required only when the file's content makes them relevant. | `human.documentation_review` |
| `DOC-002A` | Definition docstrings | `MUST` | `DIRECT_MANUAL` | `ASSISTED` | Every public definition requires a docstring that conveys its mathematical meaning. | `human.documentation_review` |
| `DOC-002B` | Major-theorem docstrings | `MUST` | `DIRECT_MANUAL` | `HUMAN` | Every major theorem requires a docstring; deciding whether a theorem is major is contextual. | `human.documentation_review` |
| `DOC-002C` | Structure and class field documentation | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Each newly introduced explicit structure or class field should have a docstring by default. Limited exceptions are generated fields, declarations that only `extends` documented parents without new explicit fields, and genuinely self-evident fields with sufficient context. | `human.documentation_review` |
| `DOC-002D` | Useful lemma docstrings | `PREFER` | `DIRECT_MANUAL` | `HUMAN` | Add docstrings to ordinary lemmas when they carry mathematical content or are likely to be useful across files. | `human.documentation_review` |
| `DOC-003` | Mathematical meaning | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Write documentation in English and state the mathematical meaning accurately; implementation details may be abstracted away but not confused with semantics. | `human.documentation_review` |
| `DOC-004` | Sentence and theorem formatting | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | If a docstring is a complete sentence, end it with a period, and boldface named mathematical theorems according to the documentation convention. `linter.style.docString` checks only mechanical delimiter, emptiness, leading/trailing whitespace, comma, and trailing newline form; sentence punctuation, theorem-name boldface, and general prose remain human review. | `linter.style.docString`, `human.documentation_review` |
| `DOC-005` | Cross-references | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Put current Lean 4 declaration names in backticks, use real fully qualified names such as `Set.mem_iUnion₂` when stable linking matters, and cross-reference related declarations explicitly. Backtick formatting does not prove resolution: the planned `custom.doc_link_check` resolves exact names in the pinned environment, while namespace-relative, protected, alias, ambiguous, and unresolved names require separate handling and human review. | `custom.doc_link_check`, `human.documentation_review` |
| `DOC-006` | Proof sketches and comments | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | Provide a proof sketch for complex or non-obvious proofs and mark mathematical stages with comments rather than leaving only a tactic sequence. | `human.documentation_review` |
| `DOC-007` | Warnings and scope | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | Mark auxiliary, hazardous, or narrowly applicable declarations clearly in their name or documentation so they are not mistaken for preferred public API. | `human.documentation_review` |
| `DOC-008` | Literature references | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Record the source and relevance of literature-backed formalizations, adding new bibliography entries to docs/references.bib. | `custom.bibliography_reference_check`, `human.documentation_review` |
| `STM-001` | Hypotheses left of colon | `PREFER` | `DIRECT_MANUAL` | `HUMAN` | When a proof begins by introducing variables and hypotheses, prefer parameters to the left of the colon over outermost ∀ or →. | `human.statement_review` |
| `STM-002` | Avoid conjunction hypotheses | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Normally split a P ∧ Q hypothesis into separate hP and hQ arguments to improve lemma usability. | `human.statement_review` |
| `STM-003` | Split conjunction conclusions | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | Public lemmas should normally expose Q and R separately rather than return Q ∧ R; a private conjunction lemma may share the proof. | `human.statement_review` |
| `STM-004` | Avoid disjunction hypotheses | `PREFER` | `DIRECT_MANUAL` | `HUMAN` | Usually split an S ∨ T hypothesis into two lemmas, retaining the disjunction only when splitting would create excessive duplication. | `human.statement_review` |
| `STM-005` | Canonical normal forms | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | State results in the canonical normal form and rewrite orientation used by existing mathlib APIs. | `human.statement_review` |
| `PRF-001` | Reuse existing lemmas | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | Search for existing or more general results before proving a new one, and prefer composing public API over reproving a special case. | `human.proof_review` |
| `PRF-002` | Decompose long proofs | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | Decompose long proofs into named, reusable mathematical lemmas; do not hide structure merely to reduce line count. | `human.proof_review` |
| `PRF-003` | Readable tactic choice | `PREFER` | `REVIEW_HEURISTIC` | `HUMAN` | Choose tactics that express mathematical intent and remain robust under refactoring; code golf is an improvement only when readability is preserved. | `human.proof_review` |
| `PRF-004` | Stable proof structure | `CONTEXT` | `SYNTHESIZED_GUIDANCE` | `HUMAN` | Treat fragile unfolding, unusual transparency, repeated `erw`, or unexplained extra `rfl` steps as review signals—not automatic violations—that may indicate a missing API lemma or a noncanonical normal form. | `human.proof_review` |
| `PRF-005` | No unused tactic steps | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | Remove tactic calls that do not change the proof state, except for the pinned linter’s documented whitelist and exclusions. | `linter.unusedTactic` |
| `PRF-006` | Avoid deprecated Lean-3-style tactics | `SHOULD` | `DIRECT_MANUAL` | `DETERMINISTIC` | Avoid `refine'`, `cases'`, and `induction'`; use the corresponding Lean 4 tactics unless a documented incompatibility requires otherwise. | `linter.style.refine`, `linter.style.cases`, `linter.style.induction` |
| `PRF-007` | No native_decide in mathlib proofs | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | Do not use `native_decide` or `decide +native` in mathlib proof code. Hard validation combines `linter.style.nativeDecide`—a first-line syntax check with documented false negatives, including some `decide (config := ...)` forms—with the pinned `lake env leanchecker --fresh Mathlib` kernel/environment gate or an adopted equivalent. | `linter.style.nativeDecide`, `checker.leanchecker` |
| `API-001` | Complete usable API | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | Provide the constructors, eliminators, extensionality lemmas, simp/rewrite lemmas, and attributes that are actually needed for downstream use, so users need not unfold implementation details. | `human.api_review` |
| `API-002` | Propositional API over definitional accidents | `CONTEXT` | `SYNTHESIZED_GUIDANCE` | `HUMAN` | Prefer a stable propositional API when downstream users would otherwise have to rely on accidental definitional equality. Repeated `erw` or extra `rfl` steps are evidence to investigate, not a universal failure criterion. | `human.api_review` |
| `API-003` | Appropriate generality | `CONTEXT` | `REVIEW_HEURISTIC` | `HUMAN` | State results at the natural level of generality consistent with the literature and existing abstractions, without sacrificing usability for formal maximality. | `human.api_review` |
| `API-004` | Standard bundling patterns | `CONTEXT` | `SYNTHESIZED_GUIDANCE` | `HUMAN` | Reuse established bundling abstractions—such as bundled morphisms, `FunLike`, or `SetLike`—when they genuinely match the object being modeled. Do not impose these patterns universally, and avoid unnecessary dependent types or typeclass diamonds. | `human.api_review` |
| `API-005` | Appropriate attributes | `CONTEXT` | `REVIEW_HEURISTIC` | `HUMAN` | Add or omit attributes such as `@[simp]`, `@[ext]`, and `@[simps]` according to the intended API and canonical forms; attributes are not automatically beneficial. | `human.api_review` |
| `API-006` | Instance diamond safety | `CONTEXT` | `REVIEW_HEURISTIC` | `HUMAN` | Check new instances for non-definitional or non-propositional diamonds and for unintended inference paths. | `human.api_review` |
| `API-007` | Transformation parity | `SHOULD` | `SYNTHESIZED_GUIDANCE` | `ASSISTED` | Where applicable, use transformation automation such as `@[to_additive]` or duality generation and preserve generated API and naming parity. Contextual exceptions include `to_additive existing`, an existing companion declaration, unsupported constants, necessary naming overrides, and generation that would create an incorrect or unstable API. | `human.api_review` |
| `LOC-001` | Correct home file | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | Place a declaration in a mathematically appropriate file as high in the import hierarchy as its dependencies permit. Use `#find_home` as evidence, not as an infallible placement oracle. | `command.#find_home`, `human.location_review` |
| `LOC-002A` | Import minimization | `SHOULD` | `REVIEW_HEURISTIC` | `ASSISTED` | Avoid unnecessary or oversized imports. Use `#min_imports in` for a one-command/term experiment that looks upward for dependencies, noting its attribute/example limits; use incremental `linter.minImports` via `#import_bumps` from the activation point downward to track import growth across later commands. Both are assisted evidence and neither proves global architectural minimality. | `command.#min_imports_in`, `linter.minImports`, `command.#redundant_imports`, `human.location_review` |
| `LOC-002B` | Dependency direction | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | Preserve the intended dependency direction from foundational modules to higher-level modules; a locally minimal import set is not sufficient if it creates an architectural cycle or inversion. | `human.location_review` |
| `LOC-003` | Duplicate and general-result search | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | Before adding a declaration, search for identical, equivalent, or more general results using tools such as `exact?`, `apply?`, `#check`, and repository search. | `human.location_review` |

### 5.1 Phase 3 exceptions, examples, and benchmark label boundaries

- `FIL-003`: score alphabetical order only within ordinary `public import` and
  `import` blocks; do not invent a total order for `public meta import` or
  `import all`.
- `FIL-008`: `Mathlib.Tactic` remains a hard negative. A `Lake.*` import with
  recorded necessity, performance evidence, and a justified linter allowance
  is a warning/review case, not an unconditional hard negative.
- `FMT-005`: `def f x := x` obscures a public signature and should become
  `def f (x : α) : α := x`; `{n}` and `{m}` are accepted when a typed dependent
  context makes their types clear.
- `FMT-011`: deterministic empty-line labels apply only to syntax nodes and
  paths covered by the pinned linter. Excluded contexts receive assisted/human
  readability labels.
- `FMT-012`: label only the exact development, debt, deprecated, or unscoped
  option classes named above as deterministic failures. Other narrowly scoped
  technical options require necessity review; tests may record allowances.
- `FMT-019`: record character/variant legality separately from mathematical
  readability, and never transfer an allow-list judgment across Mathlib
  snapshots without repinning.
- `DOC-001C`: score a missing section only when the file makes that conditional
  section relevant; never require every named section mechanically.
- `DOC-002C`: an undocumented new explicit law or data field is a default
  violation; generated, `extends`-only, and rare genuinely self-evident cases
  are explicit exceptions.
- `DOC-004`: keep deterministic docstring-mechanics labels separate from human
  sentence-punctuation, theorem-boldface, and prose labels.
- `DOC-005`: separate backtick formatting from exact-name resolution. Future
  cases must cover namespaces, protected names, aliases, successful resolution,
  ambiguity, and unresolved backticks.
- `PRF-007`: syntax-linter success alone cannot accept a case. Probe documented
  syntax boundaries and require the independent checker gate.
- `API-007`: ordinary missing transformation parity is a `SHOULD` finding;
  `existing`, existing-companion, unsupported-constant, naming-override, and
  generated-API-hazard cases are contextual exceptions.
- `LOC-002A`: LOCATE/DETECT labels must distinguish tool output from the human
  dependency-architecture judgment; neither import tool proves global
  minimality.

## 6. Hard-validation contract

Compilation alone is insufficient. Every candidate must also satisfy:

1. `lake env lean` exits with code 0;
2. candidate code contains no `sorry` or `admit`;
3. candidate code introduces no `axiom` or `constant` declaration; trusted context may occur only in a frozen prelude;
4. target declarations introduce no new axiom dependency relative to the case baseline; the global axiom set need not be empty;
5. no warning remains outside the case-specific warning allow-list;
6. any claimed statement/specification preservation is machine-checked;
7. source, logs, metadata, and validation records are linked by SHA-256;
8. native-decision trust validation passes both `linter.style.nativeDecide` and
   `lake env leanchecker --fresh Mathlib`, or a project-adopted equivalent whose
   exact invocation is recorded.

Static scans are defense in depth only. The final gate combines Lean
compilation, warning inspection, axiom deltas, pinned linters, and the checker
gate where required.

## 7. Rule-card fields

Every machine-readable leaf rule includes applicability, exceptions, a representative example, source locators, strength, automation level, validator IDs, and supported task types. Benchmark findings must target a leaf rule, not a legacy mixed alias.

## 8. Scope control

The source-coverage matrix is `../../../benchmarks/mathlib-style/manifests/COVERAGE.json`. Local variable-letter conventions are not pilot-scored; performance profiling and repository-wide migration campaigns belong to separate benchmarks; AI-use guidance is release policy rather than a code-style gold label.

## 9. Use boundary

These materials support offline evaluation and human-supervised review suggestions. LLM-generated GitHub or Zulip comments must not be published as the user's own words. For real PR cases, review prose defaults to metadata plus human-written paraphrase unless short-quotation use is separately recorded.
