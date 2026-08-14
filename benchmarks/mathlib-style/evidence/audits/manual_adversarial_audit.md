# Mathlib Style Distillation v0.3.0 — manual adversarial audit

Status: **complete (75/75 leaf rules audited)**.

## 1. Executive summary

This audit reviewed all **75** frozen v0.3.0 leaf rules in family order against Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` and contributor-policy `7b967eb1aaab674bd6aead708d42c4a83e2aca05`. It records **150 supporting citations** (two per rule) drawn from **49 exact pinned code spans**, plus one deliberate counterexample candidate and classification for every rule. No rule ID, rule text, strength, validator, fixture, case, harness, or manual was changed; the recommendations below are prospective only.

The distillation is broadly sound, but not ready to be treated as uniformly literal or uniformly machine-checkable. Thirteen rules need qualification, scope, or strength work before a later revision: five P1 findings affect false-positive risk or hard-validation claims, and eight P2 findings affect precision and benchmark labeling. No rule is marked `UNSUPPORTED`; no `RULE_SPLIT_REQUIRED` or `MERGE_CANDIDATE` was established.

Disposition totals:

- `CONFIRMED`: 6
- `CONFIRMED_WITH_EXISTING_EXCEPTIONS`: 56
- `REQUIRES_QUALIFICATION`: 8
- `SCOPE_TOO_BROAD`: 2
- `STRENGTH_TOO_STRONG`: 1
- `STRENGTH_TOO_WEAK`: 2
- `RULE_SPLIT_REQUIRED`: 0
- `MERGE_CANDIDATE`: 0
- `UNSUPPORTED`: 0

Counterexample classifications:

- `GENUINE_COUNTEREXAMPLE`: 1
- `LEGITIMATE_EXCEPTION`: 47
- `DOMAIN_SPECIFIC`: 6
- `COMPATIBILITY_CONSTRAINT`: 7
- `GENERATED_CODE`: 2
- `LEGACY_CODE`: 6
- `INCONCLUSIVE`: 6

## 2. Scope, pins, and baseline

- Mathlib release/commit: `v4.30.0` / `c5ea00351c28e24afc9f0f84379aa41082b1188f`; Lean toolchain: `leanprover/lean4:v4.30.0`; environment: `MATHLIB-4.30.0`.
- Policy snapshot: `MATHLIB-POLICY-2026-08-13`, contributor repository commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`.
- Normative artifact: `docs/research/mathlib-style/MANUAL_EN.md` v0.3.0; inventory and metadata from `benchmarks/mathlib-style/manifests/RULES.json`.
- Baseline worktree was already dirty, including unrelated EFG and untracked benchmark/research work. This audit preserves it and changes only this report.
- Explicitly out of scope: Manual EN/ZH, taxonomy, RULES/VALIDATORS/schemas/fixtures, cases/harness/evaluation, and all EFG work. No Git staging, commit, push, branch rewrite, restore, clean, or stash action was performed.

Family reconciliation: `FIL` 8, `FMT` 19, `NAM` 12, `DOC` 13, `STM` 5, `PRF` 7, `API` 7, `LOC` 4; total **75**.

## 3. Methodology and classification protocol

Each rule was checked in four layers: (1) frozen metadata and source locator; (2) exact pinned policy wording; (3) exact pinned linter/checker behavior where claimed; and (4) accepted pinned source practice. Repository-wide searches were adversarial rather than confirmatory: every rule has a recorded candidate even when the candidate ultimately proves to be an exception or remains inconclusive. Policy language is treated as guidance where the policy itself says so (P01); source occurrences are not automatically precedential, and generated/legacy/domain/compatibility cases are separated.

Classification meanings used here: `GENUINE_COUNTEREXAMPLE` conflicts with the current unqualified rule in accepted ordinary source; `LEGITIMATE_EXCEPTION` is already justified by scope or semantics; `DOMAIN_SPECIFIC` follows mathematical vocabulary/notation; `COMPATIBILITY_CONSTRAINT` is forced by Lean/import/API compatibility; `GENERATED_CODE` arises from generation; `LEGACY_CODE` is retained historical practice; `INCONCLUSIVE` lacks enough evidence to infer policy status. Dispositions use only the allowed Phase 2 vocabulary.

- **Q-FILE** — `rg --files Mathlib -g '*.lean'` plus a basename UpperCamelCase predicate; inspect the three misses and all files over 1500 lines.
- **Q-HEAD** — Inspect every pinned header/import linter branch; sample `module`, `public import`, `import`, author, and module-doc ordering with `rg -n`.
- **Q-FMT** — Search syntax/layout candidates with `rg -n` for long lines, binder omissions, `Type _`, `λ`, dollar characters, `show`, `change`, focusing dots, blank lines, options, and open `Classical`; then classify parsed context.
- **Q-NAME** — Search declarations for capitalization, British spelling, `_of_`, coercion names, `.ext`, `_injective`/`injective_`, `_inj`, `induction_on`, `recOn`, and namespace placement.
- **Q-DOC** — Inspect module/declaration docs and search missing/short/warning/reference/cross-reference candidates; compare prose to the pinned docstring linter's exact coverage.
- **Q-STMT** — Search theorem signatures for implication/quantifier placement and top-level `∧`/`∨`; distinguish logical characterizations, private helpers, and duplication-avoidance exceptions.
- **Q-PROOF** — Search proofs for reuse, long tactic blocks, semicolon chains, `erw`, extra `rfl`, deprecated tactics, `native_decide`, and linter exclusions.
- **Q-API** — Inspect representative bundled morphism/subobject/lattice APIs; search attributes, coercions, definitional-equality workarounds, universe constraints, diamonds, `to_additive`, and `to_dual`.
- **Q-LOC** — Inspect targeted imports and run text/static searches corresponding to `#find_home`, `#min_imports_in`, incremental min-imports, duplicate names, and more-general theorem vocabulary.

## 4. Exact evidence ledger

Rule entries cite ledger IDs. A citation inherits every exact field below; reuse never changes its provenance.

### 4.1 Policy anchors

- **P01** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/style.md`; lines 1-7; anchor “guidelines rather than rigid rules”; blob `4d7dc29a0edb95fd4e4bc40e2907df8670bf5466`.
- **P02** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/style.md`; lines 28-81; anchor “Unicode, line length, headers, imports, authors”; blob `4d7dc29a0edb95fd4e4bc40e2907df8670bf5466`.
- **P03** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/style.md`; lines 83-214; anchor “module docs and declaration formatting”; blob `4d7dc29a0edb95fd4e4bc40e2907df8670bf5466`.
- **P04** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/style.md`; lines 274-318; anchor “field docs, declaration separation, transformation attributes”; blob `4d7dc29a0edb95fd4e4bc40e2907df8670bf5466`.
- **P05** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/style.md`; lines 347-453; anchor “binders and statement-shape guidance”; blob `4d7dc29a0edb95fd4e4bc40e2907df8670bf5466`.
- **P06** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/style.md`; lines 455-618; anchor “calc, tactics, focusing, and short-proof exceptions”; blob `4d7dc29a0edb95fd4e4bc40e2907df8670bf5466`.
- **P07** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/style.md`; lines 646-790; anchor “transparency/API, whitespace, empty lines, normal forms, comments”; blob `4d7dc29a0edb95fd4e4bc40e2907df8670bf5466`.
- **P08** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/naming.md`; lines 5-78; anchor “file/general naming and spelling”; blob `71b7d85e0bd0c00d7938b7b513fde60dc578a4dc`.
- **P09** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/naming.md`; lines 82-299; anchor “vocabulary, coercions, namespaces, axiomatic names”; blob `71b7d85e0bd0c00d7938b7b513fde60dc578a4dc`.
- **P10** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/naming.md`; lines 301-444; anchor “conclusion-first and hypothesis naming”; blob `71b7d85e0bd0c00d7938b7b513fde60dc578a4dc`.
- **P11** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/naming.md`; lines 445-504; anchor “extensionality, injectivity, induction and recursion”; blob `71b7d85e0bd0c00d7938b7b513fde60dc578a4dc`.
- **P12** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/doc.md`; lines 10-110; anchor “module and declaration documentation requirements”; blob `b3a3d201601ec80845714de6d48521f7a34387af`.
- **P13** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/doc.md`; lines 146-285; anchor “links, sectioning, citations, and language”; blob `b3a3d201601ec80845714de6d48521f7a34387af`.
- **P14** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/pr-review.md`; lines 48-102; anchor “review questions for style, docs, location, proofs, API”; blob `b6b59e101151aeff174f6ce8d335240e52bb0002`.
- **P15** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/pr-review.md`; lines 388-462; anchor “warnings and literature references”; blob `b6b59e101151aeff174f6ce8d335240e52bb0002`.
- **P16** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/pr-review.md`; lines 464-545; anchor “home files, duplicate search, imports, splitting”; blob `b6b59e101151aeff174f6ce8d335240e52bb0002`.
- **P17** — policy commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05`; `templates/contribute/pr-review.md`; lines 547-718; anchor “proof improvement and library integration”; blob `b6b59e101151aeff174f6ce8d335240e52bb0002`.

### 4.2 Mathlib implementation and practice anchors

- **E01** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Set/Lattice.lean`; lines 1-44; anchor “header, imports, and module docstring”; blob `63d05b1804bd7785dc2f9059371e12db85080533`. Standard header/import boundary and a titled, sectioned module docstring.
- **E02** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Fintype/Order.lean`; lines 6-17; anchor “public and ordinary import blocks”; blob `616051ccc6ca7f766beb8425b6a1f868f8813f62`. Public imports precede a separate ordinary-import block.
- **E03** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Set/Lattice.lean`; lines 11-44; anchor “module docstring: The set lattice”; blob `63d05b1804bd7785dc2f9059371e12db85080533`. Title, summary, main declarations, naming notes, notation, and cross-references appear before declarations.
- **E04** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Fintype/Order.lean`; lines 121-128; anchor “Fintype.toCompleteLinearOrder docstring”; blob `616051ccc6ca7f766beb8425b6a1f868f8813f62`. The docstring states meaning and warns about an instance-diamond condition.
- **E05** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Set/Lattice.lean`; lines 58-69; anchor “Set.mem_iUnion₂ / Set.mem_iUnion_of_mem”; blob `63d05b1804bd7785dc2f9059371e12db85080533`. Names lead with conclusions, use `_of_`, and reuse established `iUnion` vocabulary.
- **E06** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Fintype/Order.lean`; lines 65-80; anchor “Fintype.toOrderBot / toOrderTop / toBoundedOrder”; blob `616051ccc6ca7f766beb8425b6a1f868f8813f62`. Type-valued constructions use lowerCamelCase and live in the supplying object namespace.
- **E07** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Set/Lattice.lean`; lines 58-65; anchor “Set.mem_iUnion₂ / Set.mem_iUnion_of_mem proofs”; blob `63d05b1804bd7785dc2f9059371e12db85080533`. Proofs reuse the indexed-union membership API rather than unfold definitions.
- **E08** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Algebra/Order/Group/Defs.lean`; lines 99-109; anchor “inv_le_self_iff family”; blob `673dacbe50feeec414e3f59e224bc63b8a200428`. Short proofs compose canonical iff lemmas and preserve the established normal form.
- **E09** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Set/Lattice.lean`; lines 50-58; anchor “universe variables and Set.mem_iUnion₂”; blob `63d05b1804bd7785dc2f9059371e12db85080533`. Arbitrary universes use `Type*`/`Sort*`; declaration binders are explicit and left of the result colon.
- **E10** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Fintype/Order.lean`; lines 88-97; anchor “Fintype.toCompleteLattice”; blob `616051ccc6ca7f766beb8425b6a1f868f8813f62`. `Classical` is scoped to one declaration and the construction follows the bundled lattice API.
- **E11** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Algebra/Algebra/Unitization.lean`; lines 1-61; anchor “file header, imports, and module overview”; blob `ae775ef7e8b4005be8463949ddb7e03cf1b6fc42`. A cohesive mathematical module documents definitions, results, design, and TODOs after targeted imports.
- **E12** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Algebra/Algebra/Unitization.lean`; lines 66-127; anchor “Unitization, equiv, injectivity API, and inclusions”; blob `ae775ef7e8b4005be8463949ddb7e03cf1b6fc42`. Bundling, extensionality, equivalence, injective/surjective/bijective lemmas, `_inj_iff`, constructors, coercion, and attributes form a usable API.
- **E13** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Analysis/Normed/Lp/PiLp.lean`; lines 387-427; anchor “pseudoEmetricAux and iSup_edist_ne_top_aux”; blob `d02183e9069d893dbe180af93e96f3543d55ec64`. Detailed warnings explain a temporary non-instance and a file-local auxiliary theorem; the proof uses structured focusing and `calc`.
- **E14** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Analysis/LocallyConvex/WithSeminorms.lean`; lines 709-760; anchor “equicontinuous_TFAE”; blob `46fa0bc06a98bf0ec262895b175276fd8195972b`. A major theorem has mathematical documentation, cross-reference, explicit binders, proof comments, focused branches, and reusable TFAE steps.
- **E15** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Analysis/Asymptotics/Defs.lean`; lines 1-54; anchor “cohesive long-file header and calibrated limit”; blob `51fddaaf99e009e6ca58c3dcfae944c7fc544d7d`. A 1525-line cohesive definitions module raises `longFile` only to 1600 and explains its API.
- **E16** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts.lean`; lines 1575-1587; anchor “end of file and calibrated longFile limit”; blob `579a1f67e7e0ce1126e6a5eba3891383cf3a3e91`. The 1587-line file uses the linter-calibrated 1700-line exception.
- **E17** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/ENNReal/Inv.lean`; lines 225-267; anchor “div/mul inverse theorem family”; blob `c14d1b7ef99f779ff9072d0aa46eef20834fa788`. Most side conditions are split; `mul_inv` and `inv_div` retain disjunctions to avoid four near-duplicate lemmas.
- **E18** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Order/CompleteLattice/Defs.lean`; lines 140-240; anchor “completeLatticeOfInf/Sup and duality”; blob `0752929adea1bfef6c223baba5b47aef2290052f`. Warnings explain poor definitional equalities and preferred construction; `to_dual` maintains symmetric APIs.
- **E19** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Algebra/Group/Defs.lean`; lines 85-140; anchor “cancellation API and to_additive generation”; blob `3f6b1f43518fe6b21f15d3a895c3656fd8d9e1d5`. Semantic names, `_injective`/`_inj`, attributes, explicit binders, and generated additive parity appear together.
- **E20** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Algebra/Group/Hom/Defs.lean`; lines 80-130; anchor “ZeroHom/AddHom and morphism classes”; blob `8e48fda8d22d0199fd56532e57ed1fa4be936921`. Bundled morphisms, protected fields, FunLike classes, field docs, and general class-parametric advice follow standard API patterns.
- **E21** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Nat/Init.lean`; lines 285-314; anchor “stepInduction, strong_induction_on, decreasingInduction”; blob `83c1987137a496ad164b708e23954b45e68dd661`. Induction naming follows result sort/argument order, while inferable `{n}` and `{m}` binder types are intentionally omitted.
- **E22** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/NumberTheory/Padics/PadicNorm.lean`; lines 1-38; anchor “canonical documentation example”; blob `77e270b970595889e19fb1fa84e9eeb2dcb88045`. Standard header, title, summary, implementation notes, bibliography-backed references, and tags.
- **E23** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Topology/MetricSpace/GromovHausdorff.lean`; lines 615-680; anchor “SecondCountableTopology GHSpace proof”; blob `70934af7912b6191b23e8989a872a1ec881bc033`. A major proof is decomposed with named intermediate data and mathematical comments explaining its structure.
- **E24** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Algebra/Category/ModuleCat/Stalk.lean`; lines 61-78; anchor “scoped heartbeat adaptation”; blob `66979c36fa0d38cbcbabd82bab84b86d0a1400d9`. An adaptation note and nested, declaration-scoped heartbeat limits document a compatibility constraint.
- **E25** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean`; lines 681-690; anchor “scoped heartbeat with explanation”; blob `b3936dabc82f22b0dd25bc8b97795b2381b539f1`. A heartbeat increase is scoped to one theorem and carries an inline date/reason.
- **E26** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Analysis/Normed/Lp/lpSpace.lean`; lines 1-34; anchor “lower-case object-named file”; blob `515909235bb8dbc24be28f6233c0eaf5336d4db9`. The lower-case file name matches the specifically lower-cased mathematical object `lp`/ℓp.
- **E27** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Analysis/InnerProductSpace/l2Space.lean`; lines 1-34; anchor “lower-case object-named file”; blob `347b70bc4b4e0a4d34c9d3fdd52f58503bc970b3`. The lower-case file name is a domain-specific exception for ℓ²-space.
- **E28** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean`; lines 98-111; anchor “`congr($(…))` syntax”; blob `352921912f0081919ee25d7d66ad01b53aa1bc9f`. Dollar characters occur in `congr` antiquotation syntax, not the prohibited application synonym for `<|`.
- **E29** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Algebra/DualNumber.lean`; lines 42-51; anchor “DualNumber result universe”; blob `089fa54f44f29642bdf570919241f58ea49709cd`. `Type _` requests elaborator-computed concrete universe behavior for a type synonym.
- **E30** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/CategoryTheory/Abelian/Images.lean`; lines 106-117; anchor “coimage_image_factorisation”; blob `d5d83a3243edcdbeb9620c41bd9bde12c92dcaa0`. A British-spelled public declaration remains in pinned source despite the American-spelling policy.
- **E31** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Condensed/Light/Sequence.lean`; lines 20-35; anchor “LightProfinite.fibre and universe limitation”; blob `3d3925d90f5d9391c1625b302711ef4c579a8b02`. A documented universe compatibility constraint and domain-established `fibre` spelling remain.
- **E32** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`; lines 61-113; anchor “SetLike subobject API, ext, injectivity”; blob `89b7e8ae8207bdbff80eabcb75d3a8838f81c293`. A bundled subobject uses SetLike, an ext lemma, and paired `_injective`/`_inj` results.
- **E33** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/EReal/Operations.lean`; lines 50-66; anchor “canonical iff results with conjunction/disjunction”; blob `d815387a89f3e8a719b0bde7c03e20fe4475a1f3`. Conjunction/disjunction conclusions are retained where they are the canonical characterization of one operation.
- **E34** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Matrix/Basis.lean`; lines 38-56; anchor “single_apply conjunction condition”; blob `38229a55747bd2ad857d10595a736792749aff3b`. A negated conjunction is an atomic matrix-index side condition, and the same conjunction is the canonical `if` guard.
- **E35** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Multiset/Basic.lean`; lines 143-155; anchor “choose_spec split projections”; blob `14ee176f8745b7ae4157f3a3fa50136bcba89d01`. A conjunction specification is accompanied by separate public projection lemmas for convenient use.
- **E36** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Tactic/Linter/TextBased/UnicodeLinter.lean`; lines 44-206; anchor “pinned Unicode allow-list”; blob `b4b7a8b9e8c9e3d01209117035eaadb318bdc843`. The actual allow-list is code-generated/current-source data with contextual variant-selector rules.
- **E37** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Tactic/Linter/Style.lean`; lines 57-664; anchor “style syntax linters”; blob `28e1aeff5fc333e0f94037f93590d62cd34a2a07`. Pinned implementations define exact scopes and exceptions for options, ends, dots, dollars, lambdas, file/line length, naming, Classical, and `show`.
- **E38** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Tactic/Linter/Header.lean`; lines 273-439; anchor “header and broad-import linter”; blob `bb8fff00908e6fe3d08041d7e23cfaf3ee85c64e`. The linter scopes header checks and treats `Mathlib.Tactic` as forbidden but `Lake` as a benchmark-and-silence warning.
- **E39** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Tactic/Linter/Whitespace.lean`; lines 13-77; anchor “whitespace linter scope”; blob `054bff27fa7fb13ba2187b6ba8d57eb6a14ed9c8`. Automation covers column-zero commands and pretty-printed declaration hypotheses, not all layout.
- **E40** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Tactic/Linter/EmptyLine.lean`; lines 68-154; anchor “empty-line exclusions”; blob `f6d1325c74655dffce099628f6e1786a6cc822c4`. The linter skips mutual/string/doc nodes, where-fields, incomplete commands, and files under Tactic/Util/Meta.
- **E41** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean`; lines 1-238; anchor “deprecated tactics and native_decide checks”; blob `aad82013bae39a6b4a1e544c9fe88241c90e31ac`. Deprecated tactics are discouraged with non-interchangeability caveats; native-decision checks are syntactic and may have false negatives.
- **E42** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Tactic/Linter/UnusedTactic.lean`; lines 1-211; anchor “unused-tactic linter”; blob `2704ae66527eaff1538d1df30e14df1ce8531a47`. The info-tree check has whitelists and deliberate exclusions for sequences, conv, and custom tactics.
- **E43** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Tactic/Linter/Multigoal.lean`; lines 1-201; anchor “multigoal linter”; blob `48f8bf73adc9ff0d87e12db3d8eb87562a9e7bab`. Goal-focusing automation excludes tactics/branches for which multi-goal behavior is expected or already closes all goals.
- **E44** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Tactic/Linter/DocString.lean`; lines 1-217; anchor “docstring syntax linter”; blob `8c245f543eba2196ca7b2674d1eaf653c1b22e00`. The linter checks delimiter spacing, emptiness, commas, and trailing whitespace/newlines, but not all prose conventions.
- **E45** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Tactic/MinImports.lean`; lines 1-284; anchor “`#min_imports_in` implementation and limitations”; blob `96d4e88a0a62a2afceae3a4aaa2d95bb6a95144a`. The command supports import-minimization experiments but documents limitations and differs from the incremental linter.
- **E46** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Init.lean`; lines 1-149; anchor “standard linter set and checker hooks”; blob `d0760e71b0bf606cd36d82a2ba155bf84ada6790`. The pinned standard set establishes which registered linters are enabled and separates kernel/checker concerns.
- **E47** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Algebra/Algebra/Unitization.lean`; lines 630-646; anchor “goal changes with `change`”; blob `ae775ef7e8b4005be8463949ddb7e03cf1b6fc42`. Proofs use `change` when switching to the intended definitional presentation of a goal.
- **E48** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Data/Multiset/ZeroCons.lean`; lines 115-153; anchor “induction/recursor naming quartet”; blob `dbe5fa97bd623730992b5b90b9b3f70cadcd8e52`. `induction`, `induction_on`, `rec`, and `recOn` track motive sort and argument order.
- **E49** — Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; `Mathlib/Algebra/Algebra/Epi.lean`; lines 120-135; anchor “injective_lift_lsmul legacy order”; blob `82b222610d691175c7757bf574805bee4daf828f`. An `injective_f`-ordered public name survives alongside the preferred `f_injective` convention.

## 5. Rule-by-rule audit

### FIL family (8)

#### FIL-001 — File naming

- **Current rule:** Lean source files should generally use UpperCamelCase names. Rare lower-case exceptions require prior discussion, and the file name should identify its mathematical topic.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `ASSISTED` via `custom.file_name_upper_camel, human.file_topic_fit`; applies to `file, module`.
- **Policy basis:** `NC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E01** and **E22**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FILE**; candidate **E26** → `DOMAIN_SPECIFIC`. The lower-case name is real but names the specifically lower-cased ℓp object, exactly the policy exception.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FIL-002A — Standard header syntax

- **Current rule:** Start a mathlib file with the standard copyright, Apache-2.0 license, and `Authors:` header syntax.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `DETERMINISTIC` via `linter.style.header`; applies to `file`.
- **Policy basis:** `SG, DOC, LIN-HEADER` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E01** and **E11**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-HEAD**; candidate **E38** → `LEGITIMATE_EXCEPTION`. The implementation exempts import-only/root cases and selected copyright checks; the current rule is about ordinary source files.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FIL-002B — Author attribution semantics

- **Current rule:** The `Authors:` list should identify substantial design/development contributors whom maintainers would contact about the file; syntax alone does not decide attribution.
- **Metadata:** strength `CONTEXT`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.authorship_attribution`; applies to `file, provenance`.
- **Policy basis:** `SG` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E01** and **E22**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-HEAD**; candidate **E01** → `INCONCLUSIVE`. A header can show an author list but source text alone cannot establish whether each contribution was significant.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FIL-003 — Module and import order

- **Current rule:** Put `module` on its own line after the header, group all `public import`s before ordinary `import`s, and try to keep each import block alphabetical.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `ASSISTED` via `linter.style.header, custom.module_import_order`; applies to `file, module`.
- **Policy basis:** `SG, DOC, LIN-HEADER` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E01** and **E02**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-HEAD**; candidate **E11** → `LEGACY_CODE`. The Unitization import list is not wholly alphabetical; no evidence establishes whether dependency grouping or history caused the order.
- **Judgment:** `REQUIRES_QUALIFICATION`; priority `P2`. Qualify ordering as applying within ordinary `public import` and `import` blocks; repeat that rare modifiers have no prescribed relative order.
- **Recommended revision:** Qualify ordering as applying within ordinary `public import` and `import` blocks; repeat that rare modifiers have no prescribed relative order.
- **Benchmark implication:** Add import-order DETECT/REPAIR cases containing `public meta import` and `import all`; do not score one invented total order.

#### FIL-005 — Import organization

- **Current rule:** Keep one import per line, preserve the public/ordinary grouping, prefer alphabetical order within groups, and remove imports shown to be redundant or unnecessary.
- **Metadata:** strength `PREFER`; evidence `DIRECT_MANUAL`; authority `MANUAL, REVIEW`; automation `ASSISTED` via `custom.module_import_order, command.#min_imports_in, command.#redundant_imports, human.location_review`; applies to `file, module`.
- **Policy basis:** `SG, PR, MINIMPORTS` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E02** and **E11**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-HEAD**; candidate **E11** → `LEGACY_CODE`. Several targeted imports are ordered by local evolution rather than a single global alphabetic rule.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FIL-006 — Top-level alignment

- **Current rule:** Keep top-level declarations and commands flush-left; do not indent the contents of namespaces or sections.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `ASSISTED` via `linter.style.whitespace`; applies to `file, module`.
- **Policy basis:** `SG, LIN-WS` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E01** and **E39**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-HEAD**; candidate **E39** → `LEGITIMATE_EXCEPTION`. The linter intentionally leaves syntax nodes with no clear formatting preference unlinted.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FIL-007 — File cohesion and size

- **Current rule:** Split files according to mathematical cohesion and dependency boundaries. Roughly 1000 lines is a reviewer signal to reconsider the split; mathlib’s `longFile` linter warns above 1500 lines, while downstream projects have no long-file limit unless configured.
- **Metadata:** strength `CONTEXT`; evidence `REVIEW_HEURISTIC`; authority `LINTER, REVIEW`; automation `ASSISTED` via `linter.style.longFile, human.location_review`; applies to `file, module`.
- **Policy basis:** `PR, LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E15** and **E16**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FILE**; candidate **E15** → `LEGITIMATE_EXCEPTION`. The cohesive 1525-line definitions file exceeds the reviewer signal but uses a calibrated linter exception.
- **Judgment:** `CONFIRMED`; priority `—`. Pinned policy, implementation, and ordinary source practice align; the candidate does not create a competing rule.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FIL-008 — Header-level prohibited imports

- **Current rule:** Do not introduce imports that the pinned header linter rejects, including `Mathlib.Tactic` bucket imports or `Lake` imports in ordinary mathlib files.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `LINTER`; automation `DETERMINISTIC` via `linter.style.header`; applies to `file, imports`.
- **Policy basis:** `LIN-HEADER` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E38** and **E11**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-HEAD**; candidate **E38** → `LEGITIMATE_EXCEPTION`. A `Lake` import may be retained after necessity review, benchmarking, and explicit linter silencing; it is not the same hard rejection as `Mathlib.Tactic`.
- **Judgment:** `STRENGTH_TOO_STRONG`; priority `P1`. Revise the rule so `Mathlib.Tactic` bucket imports are rejected while `Lake.*` imports require necessity review, benchmarking, and a justified linter allowance; the unconditional MUST applies only to the former.
- **Recommended revision:** Revise the rule so `Mathlib.Tactic` bucket imports are rejected while `Lake.*` imports require necessity review, benchmarking, and a justified linter allowance; the unconditional MUST applies only to the former.
- **Benchmark implication:** Relabel Lake fixtures so a benchmarked, explicitly allowed import is not an unconditional failure; keep hard negative cases for `Mathlib.Tactic`.

### FMT family (19)

#### FMT-001 — Line length

- **Current rule:** Keep lines at or below 100 characters; the current linter permits documented exceptions such as lines containing URLs.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `DETERMINISTIC` via `linter.style.longLine`; applies to `file, declaration, proof`.
- **Policy basis:** `SG, LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E37** and **E14**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E37** → `LEGITIMATE_EXCEPTION`. The pinned linter exempts URLs, imports, module headers, and guard-message commands from the 100-column check.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-002 — Spaces around operators

- **Current rule:** Use spaces around :, :=, and infix operators; keep an operator at the end of the preceding line when breaking.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `ASSISTED` via `linter.style.whitespace, human.layout_review`; applies to `file, declaration, proof`.
- **Policy basis:** `SG, LIN-WS` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E39** and **E19**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E39** → `LEGITIMATE_EXCEPTION`. Pretty-printer comparison deliberately skips syntax whose formatting preference is ambiguous.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-003 — Indentation

- **Current rule:** Use two-space continuation indentation in general, four spaces for continued theorem statements, and two spaces for proof bodies.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `ASSISTED` via `human.layout_review`; applies to `file, declaration, proof`.
- **Policy basis:** `SG, LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E09** and **E14**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E39** → `LEGITIMATE_EXCEPTION`. Indentation automation covers declaration heads and command starts, not every expression body.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-004 — Placement of by and calc

- **Current rule:** Place by and calc on the line immediately preceding the proof or calculation, not on a line by themselves.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `ASSISTED` via `human.layout_review`; applies to `file, declaration, proof`.
- **Policy basis:** `SG, LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E08** and **E14**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E21** → `LEGITIMATE_EXCEPTION`. Equation-compiler branches place proof terms according to pattern syntax rather than the ordinary `:= by` template.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-005 — Explicit declaration types

- **Current rule:** Give explicit types for declaration parameters and return values even when Lean can infer them.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `HUMAN` via `human.statement_review`; applies to `file, declaration, proof`.
- **Policy basis:** `SG, LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E09** and **E12**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E21** → `GENUINE_COUNTEREXAMPLE`. Pinned, non-generated source omits inferable types on `{n}` and `{m}` in public declarations despite the rule’s unqualified wording.
- **Judgment:** `SCOPE_TOO_BROAD`; priority `P1`. Restrict explicit-type review to public declaration parameters/returns whose types are not already clear from a typed dependent context; record inferable index/universe binders as exceptions.
- **Recommended revision:** Restrict explicit-type review to public declaration parameters/returns whose types are not already clear from a typed dependent context; record inferable index/universe binders as exceptions.
- **Benchmark implication:** Add accepted cases like `{n}`/`{m}` in dependent declarations and reject only omissions that materially obscure the public signature.

#### FMT-006 — Binder formatting

- **Current rule:** Put a space after binders and normally state binder types explicitly.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `ASSISTED` via `linter.style.whitespace, human.layout_review`; applies to `file, declaration, proof`.
- **Policy basis:** `SG, LIN-WS, LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E09** and **E19**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E21** → `LEGITIMATE_EXCEPTION`. The rule says “normally”; inferable dependent indices are a recurring readable exception.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-007 — Anonymous functions

- **Current rule:** Use `fun`, not `λ`, for anonymous functions. The `↦` arrow is only a slight source-code preference, not a hard requirement.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `DETERMINISTIC` via `linter.style.lambdaSyntax`; applies to `file, declaration, proof`.
- **Policy basis:** `SG, LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E37** and **E14**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E36** → `DOMAIN_SPECIFIC`. The character `λ` is allowed Unicode data and appears as an identifier/doc character, but no parsed anonymous-function use was found.
- **Judgment:** `CONFIRMED`; priority `—`. Pinned policy, implementation, and ordinary source practice align; the candidate does not create a competing rule.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-008 — Application syntax

- **Current rule:** Do not use `$` for function application in mathlib source; use `<|` instead.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `LINTER`; automation `DETERMINISTIC` via `linter.style.dollarSyntax`; applies to `file, declaration, proof`.
- **Policy basis:** `LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E37** and **E14**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E28** → `DOMAIN_SPECIFIC`. `$` inside `congr($(…))` is tactic antiquotation, not application syntax and must not be auto-repaired to `<|`.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-009 — Goal focusing

- **Current rule:** Normally focus proof goals explicitly, often with `·`, so a tactic does not unintentionally act on several goals; use documented multi-goal combinators only when intentional.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `ASSISTED` via `linter.style.multiGoal, human.proof_review`; applies to `file, declaration, proof`.
- **Policy basis:** `SG, LIN-MULTI` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E43** and **E14**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E43** → `LEGITIMATE_EXCEPTION`. Some tactics intentionally operate on all goals or close all goals, so the multigoal linter excludes them.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-010 — One tactic per line

- **Current rule:** Normally place one tactic per line; compress short steps only when this clearly improves readability.
- **Metadata:** strength `PREFER`; evidence `DIRECT_MANUAL`; authority `MANUAL, REVIEW`; automation `HUMAN` via `human.proof_review`; applies to `file, declaration, proof`.
- **Policy basis:** `SG, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E14** and **E23**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E14** → `LEGITIMATE_EXCEPTION`. Short sequences expressing one mathematical idea remain readable within a branch.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-011 — No blank lines inside declarations

- **Current rule:** Do not use blank lines to segment a declaration; use comments to explain proof structure.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `DETERMINISTIC` via `linter.style.emptyLine`; applies to `file, declaration, proof`.
- **Policy basis:** `SG, LIN-EMPTY` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E40** and **E14**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E40** → `LEGITIMATE_EXCEPTION`. Pinned automation allows blank lines in mutual/string/doc/where contexts and skips Tactic/Util/Meta files.
- **Judgment:** `SCOPE_TOO_BROAD`; priority `P1`. Mirror the pinned linter scope: exclude doc/module docs, mutual/string syntax, `where` fields, incomplete commands, and Tactic/Util/Meta path segments; downgrade automation outside that scope.
- **Recommended revision:** Mirror the pinned linter scope: exclude doc/module docs, mutual/string syntax, `where` fields, incomplete commands, and Tactic/Util/Meta path segments; downgrade automation outside that scope.
- **Benchmark implication:** Partition fixtures by syntax node and path. Deterministic labels apply only where the pinned linter runs.

#### FMT-012 — Scoped production options

- **Current rule:** Do not leave development-only options or unscoped heartbeat/flexible settings in polished code; scope genuinely necessary options to the smallest command.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `LINTER`; automation `DETERMINISTIC` via `linter.style.setOption`; applies to `file, command`.
- **Policy basis:** `LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E37** and **E24**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E24** → `COMPATIBILITY_CONSTRAINT`. Production code sometimes requires scoped technical options; the adaptation note documents why.
- **Judgment:** `REQUIRES_QUALIFICATION`; priority `P2`. Name the exact option families checked by `linter.style.setOption`; distinguish forbidden debugging options from options that are permitted only when scoped.
- **Recommended revision:** Name the exact option families checked by `linter.style.setOption`; distinguish forbidden debugging options from options that are permitted only when scoped.
- **Benchmark implication:** Do not label every production `set_option` as a failure; add scoped technical-option and test-file exception cases.

#### FMT-013 — Closed sections and namespaces

- **Current rule:** Close sections and namespaces before end-of-file, except for the documented outermost public/meta/noncomputable section exceptions.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `LINTER`; automation `DETERMINISTIC` via `linter.style.missingEnd`; applies to `file`.
- **Policy basis:** `LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E37** and **E11**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E37** → `LEGITIMATE_EXCEPTION`. Outermost anonymous public/meta/noncomputable sections may intentionally remain open.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-014 — Focusing-dot syntax

- **Current rule:** Use the `·` focusing character rather than a plain dot, and do not isolate the focusing dot on a line by itself.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `LINTER`; automation `DETERMINISTIC` via `linter.style.cdot`; applies to `proof`.
- **Policy basis:** `LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E37** and **E14**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E37** → `LEGITIMATE_EXCEPTION`. Projection/dot notation is not a focusing dot; syntax-aware validation is required.
- **Judgment:** `CONFIRMED`; priority `—`. Pinned policy, implementation, and ordinary source practice align; the candidate does not create a competing rule.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-015 — Scoped Classical opening

- **Current rule:** Do not use file-wide `open Classical`/`open scoped Classical` when a declaration-local scope suffices.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER`; automation `DETERMINISTIC` via `linter.style.openClassical`; applies to `file, declaration`.
- **Policy basis:** `LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E10** and **E37**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E10** → `LEGITIMATE_EXCEPTION`. `open Classical in` is a deliberate declaration-scoped use rather than a global opening.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-016 — Use change for goal changes

- **Current rule:** When a `show` command changes the goal rather than merely presenting it, use `change` as required by the pinned style linter.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `LINTER`; automation `DETERMINISTIC` via `linter.style.show`; applies to `proof`.
- **Policy basis:** `LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E37** and **E47**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E47** → `LEGITIMATE_EXCEPTION`. `show` that only presents the existing goal remains allowed; `change` is required only when the goal actually changes.
- **Judgment:** `CONFIRMED`; priority `—`. Pinned policy, implementation, and ordinary source practice align; the candidate does not create a competing rule.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-017 — Heartbeat changes require scope and explanation

- **Current rule:** A `maxHeartbeats`-family option must be scoped to a command and accompanied by a comment explaining why the increase is necessary.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `LINTER`; automation `DETERMINISTIC` via `linter.style.setOption, linter.style.maxHeartbeats`; applies to `command`.
- **Policy basis:** `LIN-STYLE, LIN-DEP` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E24** and **E25**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E24** → `COMPATIBILITY_CONSTRAINT`. A pinned Lean behavior regression can justify scoped heartbeat changes with an adaptation note.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-018 — Use Type* for arbitrary universes

- **Current rule:** Use `Type*` rather than `Type _` when the intention is an arbitrary universe level, unless a concrete metavariable behavior is required and justified.
- **Metadata:** strength `SHOULD`; evidence `REVIEW_HEURISTIC`; authority `REVIEW`; automation `HUMAN` via `human.statement_review`; applies to `binder, declaration`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E09** and **E29**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E29** → `LEGITIMATE_EXCEPTION`. `Type _` is appropriate when the result universe must be computed from the implementation.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### FMT-019 — Readable allowed Unicode

- **Current rule:** Use Unicode where it improves mathematical notation, but reject direction-changing, invisible, modifying, or non-allow-listed characters.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `MANUAL, LINTER`; automation `ASSISTED` via `custom.unicode_allowlist, human.layout_review`; applies to `file, documentation, notation`.
- **Policy basis:** `SG` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E36** and **E14**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-FMT**; candidate **E36** → `INCONCLUSIVE`. The allow-list is mutable, context-sensitive code and is not registered in SOURCES/VALIDATORS under its actual pinned implementation path.
- **Judgment:** `REQUIRES_QUALIFICATION`; priority `P1`. Replace the untraceable custom-only validator story with the actual pinned `TextBased.UnicodeLinter` and allow-list source; state that readability remains human review and the allow-list is snapshot-specific.
- **Recommended revision:** Replace the untraceable custom-only validator story with the actual pinned `TextBased.UnicodeLinter` and allow-list source; state that readability remains human review and the allow-list is snapshot-specific.
- **Benchmark implication:** Pin Unicode fixtures to both `TextBased.lean` and `UnicodeLinter.lean`, including selector context and replacement behavior.

### NAM family (12)

#### NAM-001 — Semantic capitalization

- **Current rule:** Use snake_case for propositions and theorems, UpperCamelCase for types in Prop/Type/Sort, and usually lowerCamelCase for other Type-valued terms.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `ASSISTED` via `linter.style.nameCheck, environment_linter.defsWithUnderscore, human.naming_review`; applies to `declaration, field, constructor`.
- **Policy basis:** `NC, LIN-STYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E06** and **E12**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-NAME**; candidate **E20** → `LEGITIMATE_EXCEPTION`. Protected structure fields follow return-value semantics and generated/local symmetry, not a simple token-case regex.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### NAM-002 — Function names follow return type

- **Current rule:** Choose a function's capitalization from the semantic category of its return type, not merely from the fact that it is a function.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.naming_review`; applies to `declaration, field, constructor`.
- **Policy basis:** `NC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E06** and **E12**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-NAME**; candidate **E12** → `LEGITIMATE_EXCEPTION`. Generated projections and coercions can inherit names whose casing is constrained by surrounding API.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### NAM-003 — Fields and constructors

- **Current rule:** Apply the same semantic naming rules to structure fields and constructors as to ordinary declarations.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.naming_review`; applies to `declaration, field, constructor`.
- **Policy basis:** `NC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E19** and **E20**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-NAME**; candidate **E20** → `LEGITIMATE_EXCEPTION`. Law fields use proposition-style snake_case and a trailing prime; data fields use lowerCamelCase.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### NAM-004 — American spelling

- **Current rule:** Use American English spelling in declaration names; documentation prose may use any common English spelling.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.naming_review`; applies to `declaration, field, constructor`.
- **Policy basis:** `NC, DOC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E11** and **E25**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-NAME**; candidate **E30** → `LEGACY_CODE`. `coimage_image_factorisation` is a genuine British-spelled public name retained in pinned source.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### NAM-005 — Conclusion-first theorem names

- **Current rule:** Name a theorem primarily after its conclusion rather than its proof method or a full restatement of its hypotheses.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL, REVIEW`; automation `HUMAN` via `human.naming_review`; applies to `declaration, field, constructor`.
- **Policy basis:** `NC, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E05** and **E08**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-NAME**; candidate **E19** → `LEGITIMATE_EXCEPTION`. Axiomatic names such as cancel/comm/assoc describe structural laws instead of literally spelling the conclusion.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### NAM-006 — Hypotheses after of

- **Current rule:** When hypotheses must appear in a theorem name, place them after _of_ in statement order.
- **Metadata:** strength `PREFER`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.naming_review`; applies to `declaration, field, constructor`.
- **Policy basis:** `NC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E05** and **E23**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-NAME**; candidate **E05** → `LEGITIMATE_EXCEPTION`. Obvious or conventional hypotheses may be omitted from a name even when `_of_` is available.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### NAM-007 — Standard vocabulary

- **Current rule:** Reuse mathlib's standard symbol vocabulary, such as mul, add, one, zero, le, and lt, instead of inventing synonymous abbreviations.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL, REVIEW`; automation `HUMAN` via `human.naming_review`; applies to `declaration, field, constructor`.
- **Policy basis:** `NC, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E05** and **E19**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-NAME**; candidate **E30** → `LEGACY_CODE`. Legacy vocabulary can survive for compatibility and should not be mechanically renamed without deprecation planning.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### NAM-008 — Namespaces and dot notation

- **Current rule:** Place declarations in the natural namespace and support useful dot notation when they belong to a type or object; avoid repeating context in long names.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL, REVIEW`; automation `HUMAN` via `human.naming_review`; applies to `declaration, field, constructor`.
- **Policy basis:** `NC, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E06** and **E20**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-NAME**; candidate **E20** → `LEGITIMATE_EXCEPTION`. Namespace placement follows dot-notation usefulness and owning-object API, not merely the result type’s namespace.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### NAM-009 — Coercion names

- **Current rule:** Name coercion declarations after their underlying function rather than hiding semantics behind a generic coe name.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.naming_review`; applies to `declaration, field, constructor`.
- **Policy basis:** `NC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E20** and **E32**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-NAME**; candidate **E20** → `LEGITIMATE_EXCEPTION`. Protected `toFun` fields coexist with reducible coercions; coercion lemmas are named after the underlying function, not a generic `coe` token.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### NAM-010A — Extensionality names

- **Current rule:** Use established extensionality names such as `.ext` and `.ext_iff`, together with appropriate attributes when justified.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `ASSISTED` via `human.naming_review, human.api_review`; applies to `theorem, attribute`.
- **Policy basis:** `NC, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E12** and **E32**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-NAME**; candidate **E12** → `GENERATED_CODE`. `@[ext]` on a structure may generate projection-based extensionality; a hand-written coercion form can coexist.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### NAM-010B — Injectivity names

- **Current rule:** Follow established injectivity naming patterns such as `f_injective` and `f_inj` according to the theorem shape.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.naming_review`; applies to `theorem`.
- **Policy basis:** `NC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E12** and **E32**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-NAME**; candidate **E49** → `LEGACY_CODE`. The pinned tree still contains `injective_f` order, explicitly acknowledged as legacy by the naming guide.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### NAM-010C — Induction and recursor names

- **Current rule:** Respect the established distinction and parameter-order conventions for induction principles and recursors.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.naming_review`; applies to `theorem, recursor`.
- **Policy basis:** `NC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E21** and **E48**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-NAME**; candidate **E48** → `LEGITIMATE_EXCEPTION`. Disambiguating primes/variants are allowed while the motive sort and argument-order signal remain intact.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

### DOC family (13)

#### DOC-001A — Module docstring presence and position

- **Current rule:** Except for the documented import-only and initialization exceptions, the first non-import command must be a module docstring.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `DETERMINISTIC` via `linter.style.header`; applies to `file, module_docstring`.
- **Policy basis:** `DOC, LIN-HEADER` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E03** and **E22**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E38** → `LEGITIMATE_EXCEPTION`. Import-only files are explicitly exempt from the first-command module-doc requirement.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### DOC-001B — Module title and summary

- **Current rule:** A module docstring must contain a first-level title and a useful summary of the file’s mathematical contents.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.documentation_review`; applies to `module_docstring`.
- **Policy basis:** `SG, DOC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E03** and **E22**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E26** → `LEGITIMATE_EXCEPTION`. A mathematical-symbol title such as “ℓp space” can be concise while the following paragraphs carry the summary.
- **Judgment:** `CONFIRMED`; priority `—`. Pinned policy, implementation, and ordinary source practice align; the candidate does not create a competing rule.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### DOC-001C — Relevant module sections

- **Current rule:** Include the conventional module-docstring sections in the documented order when they are relevant; omit optional sections only when their content is absent.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.documentation_review`; applies to `module_docstring`.
- **Policy basis:** `DOC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E03** and **E11**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E26** → `LEGITIMATE_EXCEPTION`. Only relevant sections should appear; notation/references may be absent when the file has none.
- **Judgment:** `REQUIRES_QUALIFICATION`; priority `P2`. Explicitly mark Main definitions/Main statements as optional and Notation/References/Tags as conditional; avoid implying every named section is required.
- **Recommended revision:** Explicitly mark Main definitions/Main statements as optional and Notation/References/Tags as conditional; avoid implying every named section is required.
- **Benchmark implication:** Score missing sections only when file content makes the section relevant.

#### DOC-002A — Definition docstrings

- **Current rule:** Every public definition requires a docstring that conveys its mathematical meaning.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `ASSISTED` via `human.documentation_review`; applies to `definition`.
- **Policy basis:** `DOC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E12** and **E13**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E38** → `LEGITIMATE_EXCEPTION`. Generated/import-only infrastructure and certain internal declarations fall outside ordinary exported-definition documentation expectations.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### DOC-002B — Major-theorem docstrings

- **Current rule:** Every major theorem requires a docstring; deciding whether a theorem is major is contextual.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.documentation_review`; applies to `theorem`.
- **Policy basis:** `DOC, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E14** and **E23**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E13** → `LEGITIMATE_EXCEPTION`. A local auxiliary theorem can need a scope warning rather than a broad mathematical overview.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### DOC-002C — Structure and class field documentation

- **Current rule:** Document structure and class fields when their meaning is not already unambiguous from the surrounding declaration.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.documentation_review`; applies to `structure_field, class_field`.
- **Policy basis:** `DOC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E19** and **E20**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E12** → `LEGITIMATE_EXCEPTION`. Structures that only extend an already documented carrier can have no new explicit fields to document.
- **Judgment:** `STRENGTH_TOO_WEAK`; priority `P2`. Either strengthen to “each explicit field should have a docstring” per SG, with generated/extends/self-evident exceptions, or reclassify the present weaker rule as a distilled project judgment rather than direct manual text.
- **Recommended revision:** Either strengthen to “each explicit field should have a docstring” per SG, with generated/extends/self-evident exceptions, or reclassify the present weaker rule as a distilled project judgment rather than direct manual text.
- **Benchmark implication:** Add field-level cases that separate undocumented law/data fields from structures with no new explicit fields.

#### DOC-002D — Useful lemma docstrings

- **Current rule:** Add docstrings to ordinary lemmas when they carry mathematical content or are likely to be useful across files.
- **Metadata:** strength `PREFER`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.documentation_review`; applies to `lemma`.
- **Policy basis:** `DOC` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E04** and **E13**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E12** → `LEGITIMATE_EXCEPTION`. Routine projection equalities such as `mk_toProd` are reasonably grouped without individual docstrings.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### DOC-003 — Mathematical meaning

- **Current rule:** Write documentation in English and state the mathematical meaning accurately; implementation details may be abstracted away but not confused with semantics.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL, REVIEW`; automation `HUMAN` via `human.documentation_review`; applies to `module_docstring, declaration_docstring, proof_comments`.
- **Policy basis:** `DOC, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E04** and **E18**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E13** → `LEGITIMATE_EXCEPTION`. Docstrings may intentionally abstract from implementation details while preserving mathematical/user meaning.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### DOC-004 — Sentence and theorem formatting

- **Current rule:** If a docstring is a complete sentence, end it with a period. Boldface named mathematical theorems according to the documentation convention.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER, MANUAL`; automation `ASSISTED` via `linter.style.docString, human.documentation_review`; applies to `module_docstring, declaration_docstring, proof_comments`.
- **Policy basis:** `DOC, LIN-DOCSTYLE` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E04** and **E22**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E44** → `INCONCLUSIVE`. The pinned linter does not validate periods or boldface named-theorem prose, so assisted coverage is materially partial.
- **Judgment:** `REQUIRES_QUALIFICATION`; priority `P2`. State that `linter.style.docString` covers delimiter/whitespace mechanics only; periods and boldface theorem names remain human review.
- **Recommended revision:** State that `linter.style.docString` covers delimiter/whitespace mechanics only; periods and boldface theorem names remain human review.
- **Benchmark implication:** Split deterministic syntax labels from human prose labels instead of treating the linter as full coverage.

#### DOC-005 — Cross-references

- **Current rule:** Put Lean declaration names in backticks, use fully qualified names when stable linking matters, and cross-reference related declarations explicitly.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL, REVIEW`; automation `ASSISTED` via `linter.style.docString, custom.doc_link_check, human.documentation_review`; applies to `module_docstring, declaration_docstring, proof_comments`.
- **Policy basis:** `DOC, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E03** and **E13**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E44** → `LEGACY_CODE`. Policy examples contain historical qualification/casing conventions; link checking must use Lean 4 names and actual doc generation.
- **Judgment:** `REQUIRES_QUALIFICATION`; priority `P2`. Use current Lean 4 fully-qualified names in the guidance and make the custom link checker’s resolution semantics explicit.
- **Recommended revision:** Use current Lean 4 fully-qualified names in the guidance and make the custom link checker’s resolution semantics explicit.
- **Benchmark implication:** Add link-resolution cases for namespaces, protected names, aliases, and unresolved backticks.

#### DOC-006 — Proof sketches and comments

- **Current rule:** Provide a proof sketch for complex or non-obvious proofs and mark mathematical stages with comments rather than leaving only a tactic sequence.
- **Metadata:** strength `SHOULD`; evidence `REVIEW_HEURISTIC`; authority `MANUAL, REVIEW`; automation `HUMAN` via `human.documentation_review`; applies to `module_docstring, declaration_docstring, proof_comments`.
- **Policy basis:** `DOC, PR, SG` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E14** and **E23**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E08** → `LEGITIMATE_EXCEPTION`. A short proof composed from canonical lemmas needs no proof sketch.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### DOC-007 — Warnings and scope

- **Current rule:** Mark auxiliary, hazardous, or narrowly applicable declarations clearly in their name or documentation so they are not mistaken for preferred public API.
- **Metadata:** strength `SHOULD`; evidence `REVIEW_HEURISTIC`; authority `REVIEW`; automation `HUMAN` via `human.documentation_review`; applies to `module_docstring, declaration_docstring, proof_comments`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E13** and **E18**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E13** → `LEGITIMATE_EXCEPTION`. Warnings are needed only for real scope/usage hazards, not every exported declaration.
- **Judgment:** `CONFIRMED`; priority `—`. Pinned policy, implementation, and ordinary source practice align; the candidate does not create a competing rule.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### DOC-008 — Literature references

- **Current rule:** Record the source and relevance of literature-backed formalizations, adding new bibliography entries to docs/references.bib.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL, REVIEW`; automation `ASSISTED` via `custom.bibliography_reference_check, human.documentation_review`; applies to `module_docstring, declaration_docstring, proof_comments`.
- **Policy basis:** `SG, DOC, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E22** and **E19**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-DOC**; candidate **E23** → `LEGITIMATE_EXCEPTION`. A standard or self-contained argument need not add a literature citation when no specific source is followed.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

### STM family (5)

#### STM-001 — Hypotheses left of colon

- **Current rule:** When a proof begins by introducing variables and hypotheses, prefer parameters to the left of the colon over outermost ∀ or →.
- **Metadata:** strength `PREFER`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.statement_review`; applies to `public_declaration`.
- **Policy basis:** `SG` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E09** and **E21**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-STMT**; candidate **E48** → `LEGITIMATE_EXCEPTION`. Pattern-matching and recursor declarations naturally keep motives/quantification to the right of the colon.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### STM-002 — Avoid conjunction hypotheses

- **Current rule:** Normally split a P ∧ Q hypothesis into separate hP and hQ arguments to improve lemma usability.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.statement_review`; applies to `public_declaration`.
- **Policy basis:** `SG` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E17** and **E19**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-STMT**; candidate **E34** → `DOMAIN_SPECIFIC`. A negated conjunction is the atomic side condition needed by a matrix `if`; splitting changes the statement’s natural shape.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### STM-003 — Split conjunction conclusions

- **Current rule:** Public lemmas should normally expose Q and R separately rather than return Q ∧ R; a private conjunction lemma may share the proof.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL, REVIEW`; automation `HUMAN` via `human.statement_review`; applies to `public_declaration`.
- **Policy basis:** `SG, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E12** and **E35**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-STMT**; candidate **E33** → `DOMAIN_SPECIFIC`. An iff whose right side is a conjunction is a canonical characterization, not two independent theorem outputs.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### STM-004 — Avoid disjunction hypotheses

- **Current rule:** Usually split an S ∨ T hypothesis into two lemmas, retaining the disjunction only when splitting would create excessive duplication.
- **Metadata:** strength `PREFER`; evidence `DIRECT_MANUAL`; authority `MANUAL`; automation `HUMAN` via `human.statement_review`; applies to `public_declaration`.
- **Policy basis:** `SG` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E17** and **E19**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-STMT**; candidate **E17** → `LEGITIMATE_EXCEPTION`. The documented ENNReal disjunction avoids four nearly identical lemmas.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### STM-005 — Canonical normal forms

- **Current rule:** State results in the canonical normal form and rewrite orientation used by existing mathlib APIs.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `MANUAL, REVIEW`; automation `HUMAN` via `human.statement_review`; applies to `public_declaration`.
- **Policy basis:** `SG, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E08** and **E33**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-STMT**; candidate **E29** → `LEGITIMATE_EXCEPTION`. Definitional shape and universe computation can justify a representation that is not the globally preferred rewrite normal form.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

### PRF family (7)

#### PRF-001 — Reuse existing lemmas

- **Current rule:** Search for existing or more general results before proving a new one, and prefer composing public API over reproving a special case.
- **Metadata:** strength `SHOULD`; evidence `REVIEW_HEURISTIC`; authority `REVIEW`; automation `HUMAN` via `human.proof_review`; applies to `proof`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E07** and **E08**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-PROOF**; candidate **E14** → `LEGITIMATE_EXCEPTION`. Novel TFAE glue still requires local proof structure even when each step reuses library facts.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### PRF-002 — Decompose long proofs

- **Current rule:** Decompose long proofs into named, reusable mathematical lemmas; do not hide structure merely to reduce line count.
- **Metadata:** strength `SHOULD`; evidence `REVIEW_HEURISTIC`; authority `MANUAL, REVIEW`; automation `HUMAN` via `human.proof_review`; applies to `proof`.
- **Policy basis:** `PR, SG` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E14** and **E23**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-PROOF**; candidate **E23** → `LEGITIMATE_EXCEPTION`. A long proof can remain one theorem when named local data and comments expose a cohesive mathematical argument.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### PRF-003 — Readable tactic choice

- **Current rule:** Choose tactics that express mathematical intent and remain robust under refactoring; code golf is an improvement only when readability is preserved.
- **Metadata:** strength `PREFER`; evidence `REVIEW_HEURISTIC`; authority `REVIEW`; automation `HUMAN` via `human.proof_review`; applies to `proof`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E07** and **E14**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-PROOF**; candidate **E14** → `LEGITIMATE_EXCEPTION`. A mixed tactic/term proof can be clearer than forcing one tactic vocabulary throughout.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### PRF-004 — Stable proof structure

- **Current rule:** Treat fragile unfolding, unusual transparency, repeated `erw`, or unexplained extra `rfl` steps as review signals—not automatic violations—that may indicate a missing API lemma or a noncanonical normal form.
- **Metadata:** strength `CONTEXT`; evidence `SYNTHESIZED_GUIDANCE`; authority `MANUAL, REVIEW`; automation `HUMAN` via `human.proof_review`; applies to `proof`.
- **Policy basis:** `SG, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E08** and **E13**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-PROOF**; candidate **E13** → `COMPATIBILITY_CONSTRAINT`. Definitional-equality-sensitive instance construction sometimes needs local transparency handling; the rule is correctly contextual.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### PRF-005 — No unused tactic steps

- **Current rule:** Remove tactic calls that do not change the proof state, except for the pinned linter’s documented whitelist and exclusions.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `LINTER`; automation `DETERMINISTIC` via `linter.unusedTactic`; applies to `proof`.
- **Policy basis:** `LIN-UNUSED` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E42** and **E14**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-PROOF**; candidate **E42** → `LEGITIMATE_EXCEPTION`. The linter excludes sequences, conv, and custom tactics when info-tree accounting cannot soundly identify unused steps.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### PRF-006 — Avoid deprecated Lean-3-style tactics

- **Current rule:** Avoid `refine'`, `cases'`, and `induction'`; use the corresponding Lean 4 tactics unless a documented incompatibility requires otherwise.
- **Metadata:** strength `SHOULD`; evidence `DIRECT_MANUAL`; authority `LINTER`; automation `DETERMINISTIC` via `linter.style.refine, linter.style.cases, linter.style.induction`; applies to `proof`.
- **Policy basis:** `LIN-DEP` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E41** and **E14**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-PROOF**; candidate **E41** → `COMPATIBILITY_CONSTRAINT`. Deprecated prime tactics are discouraged, but the implementation notes that replacements are not always interchangeable.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### PRF-007 — No native_decide in mathlib proofs

- **Current rule:** Do not use `native_decide` or `decide +native` in mathlib proof code because they extend trust beyond the Lean kernel.
- **Metadata:** strength `MUST`; evidence `DIRECT_MANUAL`; authority `LINTER`; automation `DETERMINISTIC` via `linter.style.nativeDecide`; applies to `proof`.
- **Policy basis:** `LIN-DEP` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E41** and **E46**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-PROOF**; candidate **E41** → `INCONCLUSIVE`. The syntax linter documents possible false negatives for `decide +native`; kernel trust must also be enforced by lean4checker.
- **Judgment:** `REQUIRES_QUALIFICATION`; priority `P1`. Keep the trust prohibition, but list both the syntax linter and lean4checker; disclose documented `decide +native` false negatives and avoid claiming the linter alone is complete.
- **Recommended revision:** Keep the trust prohibition, but list both the syntax linter and lean4checker; disclose documented `decide +native` false negatives and avoid claiming the linter alone is complete.
- **Benchmark implication:** Hard validation must include the checker. Add syntactic variants designed to probe linter false negatives.

### API family (7)

#### API-001 — Complete usable API

- **Current rule:** Provide the constructors, eliminators, extensionality lemmas, simp/rewrite lemmas, and attributes that are actually needed for downstream use, so users need not unfold implementation details.
- **Metadata:** strength `SHOULD`; evidence `REVIEW_HEURISTIC`; authority `REVIEW`; automation `HUMAN` via `human.api_review`; applies to `definition, public_api, instance`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E12** and **E32**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-API**; candidate **E13** → `LEGITIMATE_EXCEPTION`. A deliberately file-local auxiliary declaration need not expose a complete public API.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### API-002 — Propositional API over definitional accidents

- **Current rule:** Prefer a stable propositional API when downstream users would otherwise have to rely on accidental definitional equality. Repeated `erw` or extra `rfl` steps are evidence to investigate, not a universal failure criterion.
- **Metadata:** strength `CONTEXT`; evidence `SYNTHESIZED_GUIDANCE`; authority `MANUAL, REVIEW`; automation `HUMAN` via `human.api_review`; applies to `definition, public_api, instance`.
- **Policy basis:** `SG, PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E18** and **E13**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-API**; candidate **E13** → `COMPATIBILITY_CONSTRAINT`. A temporary non-defeq structure is justified and documented while public instances restore the intended interface.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### API-003 — Appropriate generality

- **Current rule:** State results at the natural level of generality consistent with the literature and existing abstractions, without sacrificing usability for formal maximality.
- **Metadata:** strength `CONTEXT`; evidence `REVIEW_HEURISTIC`; authority `REVIEW`; automation `HUMAN` via `human.api_review`; applies to `definition, public_api, instance`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E10** and **E20**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-API**; candidate **E31** → `COMPATIBILITY_CONSTRAINT`. A known universe-polymorphism limitation can force less-general declarations with an explicit TODO.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### API-004 — Standard bundling patterns

- **Current rule:** Reuse established bundling abstractions—such as bundled morphisms, `FunLike`, or `SetLike`—when they genuinely match the object being modeled. Do not impose these patterns universally, and avoid unnecessary dependent types or typeclass diamonds.
- **Metadata:** strength `CONTEXT`; evidence `SYNTHESIZED_GUIDANCE`; authority `REVIEW`; automation `HUMAN` via `human.api_review`; applies to `definition, public_api, instance`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E20** and **E32**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-API**; candidate **E12** → `LEGITIMATE_EXCEPTION`. A semantic structure wrapper is appropriate even when it is not a morphism/FunLike object.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### API-005 — Appropriate attributes

- **Current rule:** Add or omit attributes such as `@[simp]`, `@[ext]`, and `@[simps]` according to the intended API and canonical forms; attributes are not automatically beneficial.
- **Metadata:** strength `CONTEXT`; evidence `REVIEW_HEURISTIC`; authority `REVIEW`; automation `HUMAN` via `human.api_review`; applies to `attribute, public_api`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E12** and **E19**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-API**; candidate **E19** → `GENERATED_CODE`. Transformation attributes generate companion declarations/attributes; their surface density is intentional.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### API-006 — Instance diamond safety

- **Current rule:** Check new instances for non-definitional or non-propositional diamonds and for unintended inference paths.
- **Metadata:** strength `CONTEXT`; evidence `REVIEW_HEURISTIC`; authority `REVIEW`; automation `HUMAN` via `human.api_review`; applies to `instance, typeclass_graph`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E04** and **E18**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-API**; candidate **E04** → `COMPATIBILITY_CONSTRAINT`. The preferred constructor changes precisely when it would create an instance diamond.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### API-007 — Transformation parity

- **Current rule:** When a declaration participates in transformations such as `@[to_additive]` or duality generation, preserve the expected generated API and naming parity.
- **Metadata:** strength `CONTEXT`; evidence `SYNTHESIZED_GUIDANCE`; authority `REVIEW`; automation `ASSISTED` via `human.api_review`; applies to `attribute, generated_declaration`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E19** and **E18**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-API**; candidate **E19** → `LEGITIMATE_EXCEPTION`. `to_additive existing` and custom docstrings/names are necessary where generated counterparts already exist.
- **Judgment:** `STRENGTH_TOO_WEAK`; priority `P2`. Raise the ordinary “where applicable, use transformation automation” recommendation from CONTEXT to SHOULD, retaining CONTEXT exceptions for `existing`, unsupported constants, naming overrides, and generated-API hazards.
- **Recommended revision:** Raise the ordinary “where applicable, use transformation automation” recommendation from CONTEXT to SHOULD, retaining CONTEXT exceptions for `existing`, unsupported constants, naming overrides, and generated-API hazards.
- **Benchmark implication:** Add positive/negative parity cases and explicit exceptions for existing companions and non-transformable constants.

### LOC family (4)

#### LOC-001 — Correct home file

- **Current rule:** Place a declaration in a mathematically appropriate file as high in the import hierarchy as its dependencies permit. Use `#find_home` as evidence, not as an infallible placement oracle.
- **Metadata:** strength `SHOULD`; evidence `REVIEW_HEURISTIC`; authority `REVIEW`; automation `HUMAN` via `command.#find_home, human.location_review`; applies to `file, module, import_graph, repository`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E01** and **E11**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-LOC**; candidate **E26** → `DOMAIN_SPECIFIC`. The lpSpace module location/name reflects a domain object and import hierarchy; `#find_home` alone cannot infer this design choice.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### LOC-002A — Import minimization

- **Current rule:** Avoid unnecessary or oversized imports; use pinned import-analysis tools as evidence and record their documented limitations.
- **Metadata:** strength `SHOULD`; evidence `REVIEW_HEURISTIC`; authority `LINTER, REVIEW`; automation `ASSISTED` via `command.#min_imports_in, linter.minImports, command.#redundant_imports, human.location_review`; applies to `imports, file`.
- **Policy basis:** `PR, MINIMPORTS, LIN-MINIMPORTS` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E02** and **E45**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-LOC**; candidate **E45** → `INCONCLUSIVE`. Min-import tools have documented limitations and different directions; a clean result is evidence, not proof of architectural minimality.
- **Judgment:** `REQUIRES_QUALIFICATION`; priority `P2`. Differentiate `#min_imports_in` experiments from the incremental `linter.minImports`; document limitations and treat both as assisted evidence.
- **Recommended revision:** Differentiate `#min_imports_in` experiments from the incremental `linter.minImports`; document limitations and treat both as assisted evidence.
- **Benchmark implication:** Separate command-output interpretation from architectural import-boundary judgments in LOCATE/DETECT tasks.

#### LOC-002B — Dependency direction

- **Current rule:** Preserve the intended dependency direction from foundational modules to higher-level modules; a locally minimal import set is not sufficient if it creates an architectural cycle or inversion.
- **Metadata:** strength `SHOULD`; evidence `REVIEW_HEURISTIC`; authority `REVIEW`; automation `HUMAN` via `human.location_review`; applies to `import_graph, architecture`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E02** and **E15**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-LOC**; candidate **E15** → `LEGITIMATE_EXCEPTION`. A large low-level definitions file can remain cohesive when splitting would worsen dependency boundaries.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

#### LOC-003 — Duplicate and general-result search

- **Current rule:** Before adding a declaration, search for identical, equivalent, or more general results using tools such as `exact?`, `apply?`, `#check`, and repository search.
- **Metadata:** strength `SHOULD`; evidence `REVIEW_HEURISTIC`; authority `REVIEW`; automation `HUMAN` via `human.location_review`; applies to `file, module, import_graph, repository`.
- **Policy basis:** `PR` in the pinned source registry. Manual locators resolve to the policy snapshot and `LIN-*` locators to pinned Mathlib; prose is interpreted under P01 rather than as an exception-free statute.
- **Supporting evidence (2):** **E07** and **E32**. Their exact commit/path/anchor/lines/blob and explanations are in §4.2.
- **Counterexample search:** **Q-LOC**; candidate **E07** → `INCONCLUSIVE`. Text/name search can miss differently named or more-general results; tactic suggestions and reviewer knowledge remain necessary.
- **Judgment:** `CONFIRMED_WITH_EXISTING_EXCEPTIONS`; priority `—`. The core guidance is supported; the candidate is an existing contextual/generated/domain/legacy exception and the current non-absolute strength is adequate.
- **Recommended revision:** No normative revision recommended for v0.3.0.
- **Benchmark implication:** No immediate benchmark relabeling; retain the cited candidate as exception/calibration evidence in any later case design.

## 6. Prioritized findings

There are no P0 findings. The following are the only recommendations that would change normative wording, strength, provenance, or benchmark labels in a future phase; none was applied here.

### P1 (5)

- **FIL-008 — `STRENGTH_TOO_STRONG`:** Revise the rule so `Mathlib.Tactic` bucket imports are rejected while `Lake.*` imports require necessity review, benchmarking, and a justified linter allowance; the unconditional MUST applies only to the former. Benchmark: Relabel Lake fixtures so a benchmarked, explicitly allowed import is not an unconditional failure; keep hard negative cases for `Mathlib.Tactic`.
- **FMT-005 — `SCOPE_TOO_BROAD`:** Restrict explicit-type review to public declaration parameters/returns whose types are not already clear from a typed dependent context; record inferable index/universe binders as exceptions. Benchmark: Add accepted cases like `{n}`/`{m}` in dependent declarations and reject only omissions that materially obscure the public signature.
- **FMT-011 — `SCOPE_TOO_BROAD`:** Mirror the pinned linter scope: exclude doc/module docs, mutual/string syntax, `where` fields, incomplete commands, and Tactic/Util/Meta path segments; downgrade automation outside that scope. Benchmark: Partition fixtures by syntax node and path. Deterministic labels apply only where the pinned linter runs.
- **FMT-019 — `REQUIRES_QUALIFICATION`:** Replace the untraceable custom-only validator story with the actual pinned `TextBased.UnicodeLinter` and allow-list source; state that readability remains human review and the allow-list is snapshot-specific. Benchmark: Pin Unicode fixtures to both `TextBased.lean` and `UnicodeLinter.lean`, including selector context and replacement behavior.
- **PRF-007 — `REQUIRES_QUALIFICATION`:** Keep the trust prohibition, but list both the syntax linter and lean4checker; disclose documented `decide +native` false negatives and avoid claiming the linter alone is complete. Benchmark: Hard validation must include the checker. Add syntactic variants designed to probe linter false negatives.

### P2 (8)

- **FIL-003 — `REQUIRES_QUALIFICATION`:** Qualify ordering as applying within ordinary `public import` and `import` blocks; repeat that rare modifiers have no prescribed relative order. Benchmark: Add import-order DETECT/REPAIR cases containing `public meta import` and `import all`; do not score one invented total order.
- **FMT-012 — `REQUIRES_QUALIFICATION`:** Name the exact option families checked by `linter.style.setOption`; distinguish forbidden debugging options from options that are permitted only when scoped. Benchmark: Do not label every production `set_option` as a failure; add scoped technical-option and test-file exception cases.
- **DOC-001C — `REQUIRES_QUALIFICATION`:** Explicitly mark Main definitions/Main statements as optional and Notation/References/Tags as conditional; avoid implying every named section is required. Benchmark: Score missing sections only when file content makes the section relevant.
- **DOC-002C — `STRENGTH_TOO_WEAK`:** Either strengthen to “each explicit field should have a docstring” per SG, with generated/extends/self-evident exceptions, or reclassify the present weaker rule as a distilled project judgment rather than direct manual text. Benchmark: Add field-level cases that separate undocumented law/data fields from structures with no new explicit fields.
- **DOC-004 — `REQUIRES_QUALIFICATION`:** State that `linter.style.docString` covers delimiter/whitespace mechanics only; periods and boldface theorem names remain human review. Benchmark: Split deterministic syntax labels from human prose labels instead of treating the linter as full coverage.
- **DOC-005 — `REQUIRES_QUALIFICATION`:** Use current Lean 4 fully-qualified names in the guidance and make the custom link checker’s resolution semantics explicit. Benchmark: Add link-resolution cases for namespaces, protected names, aliases, and unresolved backticks.
- **API-007 — `STRENGTH_TOO_WEAK`:** Raise the ordinary “where applicable, use transformation automation” recommendation from CONTEXT to SHOULD, retaining CONTEXT exceptions for `existing`, unsupported constants, naming overrides, and generated-API hazards. Benchmark: Add positive/negative parity cases and explicit exceptions for existing companions and non-transformable constants.
- **LOC-002A — `REQUIRES_QUALIFICATION`:** Differentiate `#min_imports_in` experiments from the incremental `linter.minImports`; document limitations and treat both as assisted evidence. Benchmark: Separate command-output interpretation from architectural import-boundary judgments in LOCATE/DETECT tasks.

### P3 (0)

- None.

## 7. Coverage and evidence reconciliation

- Rule coverage: **75/75 (100%)**; no skipped family and no legacy alias substituted for a leaf ID.
- Per-family counts: FIL 8/8; FMT 19/19; NAM 12/12; DOC 13/13; STM 5/5; PRF 7/7; API 7/7; LOC 4/4.
- Supporting citations: **150**, exactly two per rule; unique pinned Mathlib spans: **49**; pinned policy anchors: **17**.
- Counterexample searches: **75**, one per rule; every candidate has an allowed classification. `INCONCLUSIVE` candidates are not silently promoted to exceptions or counterexamples.
- Evidence gaps: **0 unsupported rules**. Six candidate investigations remain inconclusive (`FIL-002B`, `FMT-019`, `DOC-004`, `PRF-007`, `LOC-002A`, and `LOC-003`); each is paired with qualification or explicit human-review limits rather than an unsupported claim.
- Reconciliation against `RULES.json`: IDs, family totals, strengths, evidence classes, authorities, automation levels, validators, applies-to metadata, and source locators were read directly during report generation. The generator asserts exact equality of the 75-ID sets.

## 8. Revision and benchmark implications

A future normative revision would touch **13** rule records: `API-007, DOC-001C, DOC-002C, DOC-004, DOC-005, FIL-003, FIL-008, FMT-005, FMT-011, FMT-012, FMT-019, LOC-002A, PRF-007`. The highest-risk benchmark changes are false-positive controls for inferred binders and empty-line exclusions, separating Lake warnings from prohibited tactic-bucket imports, pinning the actual Unicode implementation, and pairing native-decision syntax checks with lean4checker. Documentation and API findings mainly require task-label precision rather than new execution infrastructure.

This audit does **not** authorize edits to the manual or manifests and does **not** create benchmark cases, fixtures, validators, harnesses, or evaluation results. Recommended labels are design notes for a later authorized phase.

## 9. Validation

Validation results are filled from commands run after report generation:

- `python3 benchmarks/mathlib-style/scripts/check_distillation.py`: **PASS** — 75 rules, 10 existing evidence anchors, 3 smoke cases/4 Lean files; pinned Mathlib verified; 11 frozen schemas hash/reference checked.
- `python3 benchmarks/mathlib-style/scripts/check_benchmark.py`: **PASS** — 3 cases, 4 Lean files, Lean 4.30.0; the script notes that final hard gates/task scoring remain intentionally unimplemented.
- `git diff --check`: **PASS**.
- final `git status --short --branch`: **REVIEWED** — the report is the only in-scope audit edit; pre-existing unrelated modified/untracked work remains preserved.

## 10. Scope confirmation and conclusion

The manual, taxonomy, manifests, validators, schemas, fixtures, cases, harness, evaluation, and EFG files were not modified. The audit used the exact pinned Mathlib and policy snapshots, preserved all pre-existing worktree changes, and performed no staging, commit, push, PR, destructive Git operation, or generated blueprint/API-site publication.

Conclusion: the Phase 2 audit is substantively complete at 75/75. The corpus is broadly supported, with a bounded set of precise revisions required before any future version claims uniform literal enforcement or complete deterministic coverage.
