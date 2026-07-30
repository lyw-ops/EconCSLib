# EFG Strict Correctness Audit

This is the single living correctness record for the current extensive-form
game implementation. Superseded cycle-specific `efg_*_audit.md` snapshots
have been removed rather than retained as competing completion evidence.

## Audit identity and scope

- Final verification snapshot: 2026-07-30 16:03 CST.
- Branch: `codex/efg-governance-closeout`.
- inspected commit: `c42e9b0`.
- Worktree: intentionally dirty, with extensive user-owned tracked and
  untracked work. No reset, checkout, clean, commit, push, or PR operation was
  performed. The evidence below applies to the complete current worktree, not
  to the inspected commit in isolation.
- Scope: representation-neutral continuation forms; observed pure,
  behavioral, and mixed EFG semantics; standard versus designated-root
  solution concepts; endpoint- versus occurrence-sensitive `GameTree`
  compilation; FOSG weak serialization; analytic measurable-kernel legality,
  paths, continuations, and restart compatibility; physical module ownership,
  public import tiers, root-aggregate boundaries, and authoritative
  documentation.
- Trust boundary: no ordinary `sorry` or `admit`, new `axiom`, `opaque`,
  `unsafe`, or `native_decide` was introduced in the EFG work. The repository's
  separately scoped `OpenProblem` marker policy and pre-existing non-EFG
  executable examples are outside this audit.

The goal is a generally reusable and semantically honest EFG framework, not a
claim that one structure literally contains every game model. Continuous time,
uncertified arbitrary conditional versions at null events, and unrestricted
imperfect-information equilibrium existence remain outside the proved layer.

## Severity convention

- P0: a false semantic certificate, a false standard-solution claim, or a
  canonical strategy space that omits claimed deviations.
- P1: a materially misleading public name, transfer boundary, hidden
  generality loss, or unstable aggregate design.
- P2: navigation, compatibility, or historical-document debt that does not
  make a current theorem false.

`Closed` means that both a source-level repair and executable Lean evidence are
present. A successful build alone is not treated as semantic evidence.

## Declaration matrix

| Declaration or family | Actual mathematical meaning and binding | Quantifiers, admitted objects, and assumptions | Vacuity / definitional-content audit | Regression or proof evidence | Severity / status |
|---|---|---|---|---|---|
| `MeasurableKernelArena` | A normalized analytic transition kernel on the measurable dependent state/action bundle. It is state-bound but not restricted to discrete or atomic laws. | Measurable state and action-bundle structures and a Markov transition kernel; no global singleton-measurability, finiteness, countability, or terminal decidability assumption. | Does not itself choose actions or assert termination. Non-atomic laws remain admitted. | `ContinuousKernelBoundary`, `ObservedNonAtomicKernelBoundary`, and exact discrete embeddings. | P0 boundary checked; closed. |
| `MeasurableKernelArena.ActionPolicy.legal` | At each nonterminal state, the selected bundled action belongs to that state's dependent action fiber almost surely under the policy kernel. | `∀ state`, local nonterminal proof, then `∀ᵐ stateAction ∂kernel state`; terminal law is zero and nonterminal law is a probability measure. | The `ae` filter, rather than outer measure of a possibly nonmeasurable fiber, is the truth source. `ae_mem_actionFiber` is intentionally a named accessor, not advertised as a deep theorem. | `NonmeasurableFiberLegalityBoundary.old_mass_one_at_false`, `not_ae_mem_falseFiber`, and `no_actionPolicy_with_badKernel`. | P0 closed. |
| `ActionPolicy.legal_mass_one` and history/event analogues | Recover the familiar numerical measure-one fiber equation from genuine almost-sure legality. | Adds only local `[MeasurableSingletonClass A.State]`, which makes the action fiber measurable. | Nontrivial conversion through `ae_mem_iff_measure_eq`; it is not used as the general legality source. The global analytic arena remains unrestricted. | `#print axioms`; discrete and restart examples; grep confirms all three primary policy layers expose `ae_mem_actionFiber`. | P0 closed. |
| `HistoryActionPolicy.legal`, `EventHistoryActionPolicy.legal` | Almost-sure legality at the latest state of a full state prefix or recorded state/action prefix. | Quantified over time and every well-typed prefix; kernels may depend on the entire prefix. | Not a Markov restriction. The latest-state fiber can still be nonmeasurable as a set, so legality remains direct `ae`. | Target compilation of history/event modules and `HistoryDependentKernelBoundary`, `EventHistoryKernelBoundary`. | P0 closed. |
| `EventInformation.RealizedActionPolicy.realization_legal` | The *bound concrete measure* obtained from abstract action selection and realization lies in the latest-state fiber almost surely. | Quantified over time, represented prefix, and local nonterminal proof; the measure is the explicit `abstractMeasure.bind realizationKernel`. | Avoids the invalid inference from nested a.e. statements through a nonmeasurable fiber. `ae_bind_mem_actionFiber_of_ae_mass_one` is only a compatibility constructor with local singleton measurability. | `RealizedInformationBoundary`, profile-assembly examples, and the nonmeasurable regression. | P0 closed. |
| `ObservedGame.Observation`, `InfoState`, `infoObserve`, `infoAt` | `Observation` is the current signal. `InfoState` is decision information or memory that projects to the current signal. | `infoAt_observe` requires equality after projection only; no injectivity of `infoObserve`. | Does not collapse memory-rich information states to observations. Perfect recall can be carried by `InfoState`. | `AbsentMinded`, `FiniteImperfectObserved`, `PerfectRecall`, and corrected module/design documentation. | P1 closed. |
| `ObservedGame.IsDesignatedContinuationRoot` | Presentation-selected roots on which conservative continuation results may be stated. | Arbitrary predicate plus proof that the initial history is designated. | May intentionally contain only the initial root. It is never, by itself, named a standard subgame certificate. The pre-release `IsSubgameRoot` alias was removed. | `DesignatedContinuationSPEBoundary.rootOnlyObserved`; the API boundary rejects the removed spelling. | P0 closed. |
| `ObservedGame.IsLawfulSubgameRoot` | The representation-internal structural criterion for one standard-subgame root: the initial history is the whole game by convention; a proper player root has singleton decision information; and information sets do not cross the continuation boundary. | Independent of the presentation's designated-root predicate. Chance and terminal proper roots have no player-information singleton obligation. | It is a proposition about one concrete history occurrence. The initial exception keeps the whole game lawful even in an absent-minded presentation, while later recurrence across the boundary is rejected. | `init_isLawfulSubgameRoot`; `AbsentMinded.firstDecision_isLawfulSubgameRoot`; `secondDecision_not_isLawfulSubgameRoot`; complete-system regressions. | P0 closed. |
| `ObservedGame.SubgameSystem` | A caller-selected system of structurally lawful roots, independent of presentation metadata. | Initial root plus the proper-root singleton-information and information-closure certificate at every selected root. | The root set cannot be empty, but it may be a conservative subset of all lawful roots. `IsPresentationVisible` separately states that its roots are designated. Results over a supplied system are named `...SubgamePerfectOn`. | `rootOnlySubgameSystem` constructs the conservative one-root system; the canonical complete-system regression admits an omitted lawful root without changing designation metadata. | P0 closed. |
| `ObservedGame.CompleteSubgameSystem` | A lawful system with converse coverage: every `IsLawfulSubgameRoot` is selected. Its selected roots are therefore exactly the structurally lawful roots. | Extends `SubgameSystem` with exact lawful-root coverage; no designation premise occurs. | `CompleteSubgameSystem.canonical` inhabits this type for every observed game. An initial-only presentation still has standard subgames; its canonical system is merely not presentation-visible. | `isRoot_iff_isLawful`, `canonical`, `rootOnlyOccurrence_completeSubgameSystem_exists`, and `rootOnlyOccurrence_canonical_not_presentationVisible`. | P0 closed. |
| `IsPureNashOnDesignatedContinuations[AtFuel]` | One complete pure profile is Nash at each presentation-designated continuation under bounded or total semantics. | Quantifies designated roots, every player, and every complete unilateral strategy; requires decidable player equality and an ordered utility codomain. Total form also requires pure termination. | Can reduce to initial-root Nash when only the initial root is designated, which is why the name says designated-continuation Nash rather than SPE. | Initial-only threat is a positive instance while its off-path local Nash theorem fails. | P0 closed. |
| `ObservedGame.IsPureSubgamePerfectOn` | Pure Nash at every root of one explicit, possibly conservative lawful `SubgameSystem`, with total termination on every selected root/profile. | Quantifies every selected root and every complete unilateral pure strategy. `PureTerminatingOn` supplies total terminal outcomes. | Nonvacuous in roots because the initial history is selected, but intentionally relative in coverage. The old unsuffixed name is a deprecated alias only. | `threat_isPureSubgamePerfectOn_rootOnly` exhibits a true relative-system result that is not standard SPE. | P0 closed. |
| `ObservedGame.IsPureStandardSubgamePerfect` | Standard pure SPE at every structurally lawful root, represented through a `CompleteSubgameSystem`. | Same deviations and termination obligations as the relative predicate; completeness adds universal lawful-root coverage. | Independent of which roots a presentation designates. Profile existence and termination remain separate theorem obligations. | `Kuhn_exists_occurrencePureSPE`; `occurrenceThreat_not_isPureStandardSubgamePerfect`; `#print axioms`. | P0 closed. |
| `ObservedGame.Iso.isPureSubgamePerfectOn_iff` and `isPureStandardSubgamePerfect_iff` | A strict observed-EFG isomorphism transports relative lawful systems or complete standard systems, termination, utility evaluation, profiles, and all pure deviations in both directions. | Requires strict history/action/information/payoff structure, no chance on both sides, local terminal decidability, and the corresponding source system. | Two-way transfer is justified by strategy equivalences. The standard theorem also transports structural lawfulness and proves completeness of the target system. | `mapLawfulSubgameRoot`, `mapCompleteSubgameSystem`, target build, and `#print axioms`. | P1 closed. |
| Structural `GameTree.IsGlobalEndpointSubgamePerfect[On]` | Optimality of one historical endpoint/global tree policy at every typed tree or every subtree value below a fixed root. | Finite no-chance tree, total preorder and decidable comparison for existence. Deviations range over endpoint-indexed strategies. | True but not the canonical occurrence-contingent standard SPE space. Primary names expose `GlobalEndpoint`; the misleading old SPE spellings have been removed. | Existing backward-induction proofs, `SimpleGameTree`, and public docs. | P0 naming/semantics closed. |
| `GameTree.toObservedGame` | Endpoint-sensitive compiler preserving the legacy `PlayerStrategy` API and its outcome semantics. | Equal subtree values at distinct occurrences share endpoint information and therefore share a decision. | Its designated-root Nash bridge is not described as an occurrence-sensitive standard-SPE equivalence. | `observed_isPureNashOnDesignatedContinuations_iff_isGlobalEndpointSubgamePerfectOn`; `OccurrenceNonIso`. | P0 closed. |
| `GameTree.toOccurrenceObservedGame`, its game-bound `PureStrategy`, and `occurrenceCompleteSubgameSystem` | Root-bound perfect-information EFG whose decision information states are player-controlled complete history occurrences; all histories form a complete lawful subgame system. | Bound to one concrete root. Strategies may condition on every distinct occurrence, including repeated equal subtree values. | No endpoint quotient is silently assumed. GameTree nodes have a nonempty child type, so constructed backward-induction actions and deviations are nonvacuous. | `OccurrenceNonIso.separatingOccurrenceStrategy_distinguishes`, occurrence/endpoint lift outcome equality, perfect-information and perfect-recall proofs. | P0 closed. |
| `GameTree.Kuhn_exists_occurrencePureSPE` | For each concrete finite root tree, constructs a complete occurrence-contingent profile satisfying `IsPureStandardSubgamePerfect` on the complete all-history system. | `∀ root`; `[DecidableEq N] [TotalPreorder U] [DecidableLE U]`; no chance. Deviations range over arbitrary occurrence strategies, not only lifted endpoint strategies. | Existence constructs an explicit profile. The profitable-deviation regression shows the deviation space has mathematical content. | `occurrenceBackwardInductionProfile_isPureStandardSubgamePerfect`, `DesignatedContinuationSPEBoundary`, and `#print axioms`. | P0 closed. |
| Endpoint/occurrence information refinement | Forgets complete occurrences to endpoint information; endpoint profiles lift with equal play and outcome. Fine-to-coarse equilibrium reflection is directional unless strategy surjectivity is supplied. | Exact dynamics and action transport; occurrence-dependent strategies generally have no endpoint representative. | Not called an isomorphism. Noninjectivity and failure of reverse strategy coverage are explicit. | `OccurrenceNonIso`; endpoint lift history/outcome laws; refinement theorem directions. | P0 closed. |
| `ContinuationGameForm.IsNashOnRoots` | Representation-neutral Nash for one shared complete profile at caller-declared roots with root-dependent utility. | Quantifies declared roots and every unilateral complete strategy. No history or information-set structure is available. | The caller may declare no roots, in which case this accurately named predicate is vacuous. Observed adapters are nonempty because they designate the initial root. The generic layer cannot certify standard subgames. Primary API is `IsDeclaredRoot`, `map_declaredRoot`, `DeclaredRootSurjective`, and `DeclaredRootReflecting`; former `SubgameRoot...` names were removed. | Generic morphism, simulation, and isomorphism builds; authoritative API migration note. | P1 closed. |
| `IndexedContinuationGameForm` and limit theorem | Reuses the same declared-root Nash layer at an arbitrary evaluator index; uniform convergence over roots, players, and deviations passes finite inequalities to an infinite payoff. | Horizon and outcome are arbitrary. The limit theorem specializes to real payoffs and requires one nonnegative error sequence tending to zero with uniform base/deviation bounds. | An empty caller-declared root predicate makes both hypotheses and conclusion vacuous, as expected for this representation-neutral layer. No finite-to-infinite claim follows without the convergence certificate, and no generic SPE claim is made. The pre-release `IsSPEForPayoff` and `isInfiniteSPE...` aliases were removed. | `InfiniteSPEBoundary` and `EFGInfrastructureApiBoundary`. | P1 closed. |
| `FiniteImperfectGame` | A compact finite-state model whose pure strategies are indexed by player-owned information sets and choose an abstract action from that information set. | The state carrier is finite; acyclicity, termination, and extra carrier finiteness are theorem-local. Every labeled decision state supplies an explicit equivalence from the shared `InfoAction` type to its concrete dependent action type. | A strategy cannot inspect the concrete state or select actions for another player's information sets. This compact presentation makes no structural finite-horizon claim. | `actionAt_same_info`, the compact example, the finite-imperfect observed compiler, target build, and `#print axioms`. | P0 closed. |
| `StochasticGameTree` | A finite-depth stochastic tree with nonempty player/chance branching, normalized chance laws represented by `PMF`, occurrence-sensitive policies, and real-valued expected payoff at an explicit fuel horizon. | Each branch type is `Fin (arity + 1)`; chance normalization and nonnegativity are structural in the `PMF`; policies receive the occurrence path. | No zero-total chance branch, arbitrary unnormalized weights, or equal-subtree occurrence collapse is admitted. Because child functions are opaque, no false theorem claims that a syntactic size bound computes the exact horizon. | `fairCoinLaw_total`, `fairCoin_expected_player0`, target build, and `#print axioms`. | P0 closed. |
| Legacy `Play` import path | Compatibility import for terminal-aware stopped execution. | General arenas use a policy that is queried only at nonterminal histories and return `Option` payoffs under finite fuel. | The former `Arena.play` total chooser, which demanded an element of the terminal state's possibly empty action type, is absent. | `RootImportBoundary`, target build of `Play`, and stopped-execution terminal regressions. | P0 removed. |
| Legacy `BehaviorStrategy` import path | Compatibility import for the canonical `Observed.Behavior` layer. | The former state-indexed reach and payoff declarations are absent. Player behavior is information-indexed and chance uses a normalized `PMF`. | The mass-losing convention that assigned probability zero at chance nodes and the assumption-repackaging state-restart theorems are no longer callable API. | Target build of the compatibility import and full-library placeholder scan. | P0 removed. |
| Behavioral/mixed finite Kuhn realization | Under finite perfect recall, behavioral randomization and independently sampled mixed contingent plans have equivalent bounded Nash on presentation-designated continuations. | Finite players and information/action hypotheses collected by `FiniteKuhnHypotheses`; bounded fuel; exact payoff-law utility. | Not a root-independent strategy-space isomorphism. Semantic deviation realization is proved at every tested root. | `isBehavioralNashOnDesignatedContinuationsAtFuel_iff_mixed`, absent-minded boundary, and `#print axioms`. | P1 closed. |
| `FOSG.WeakSerialization` and continuation bridge | One simultaneous macro step is coupled exactly to a positive finite serialized micro execution; caller-declared macro roots correspond relationally. | Chance consistency, observation/public-state preservation, exact terminal payoffs and laws, progressing weak simulation, and strategy equivalences for two-way Nash. | Not a strict isomorphism and not an automatic standard-SPE theorem. Public names say declared macro roots and macro Nash on declared continuations. | FOSG sequentialization/continuation builds and exact coupling regressions. | P1 closed. |
| Measurable absolute-prefix `IsSubgamePerfectOn` / `IsStandardSubgamePerfect` | Constructive Nash under absolute event-prefix continuation semantics, respectively on a selected lawful system or on every lawful root via a complete system. | One jointly measurable profile; measurable single-player replacements; bounded/integrable path utility; the corresponding system certificate. | Not obtained by restarting the clock. The relative/standard distinction is preserved at the analytic layer. The old unsuffixed relative name is deprecated. | `MeasurableKernelContinuationNashBoundary`, continuation-conditioning examples, and compilation. | P0 boundary checked; closed. |
| `IsFreshRestartSubgamePerfectOn` / `IsFreshRestartStandardSubgamePerfect` and compatibility equivalence | Constructive Nash after a fresh-clock restart, respectively on a selected lawful or complete system; equals its absolute-prefix counterpart only under explicit deviation-complete restart compatibility. | Compatibility quantifies the baseline and every admitted replacement profile at every selected root. | The equivalence is not definitional and does not identify clocks automatically. The standard theorem takes a complete system. | `isFreshRestartSubgamePerfectOn_iff_isSubgamePerfectOn_of_compatible`, `isFreshRestartStandardSubgamePerfect_iff_isStandardSubgamePerfect_of_compatible`, strict clock failure example, and `#print axioms`. | P0 closed. |
| Infinite discrete event-time path/payoff layer | Ionescu--Tulcea terminal-absorbing probability measure with exact finite marginals, stopping/payoff results, and uniform-deviation limit Nash. | Natural-number time; measurability and integrability/dominance where used; a.s. termination only for the theorems that require it. | Does not claim continuous time, pointwise conditioning at null events, or standard SPE without a lawful root adapter. | `RandomTermination`, infinite-path examples, exact marginal builds. | P1 boundary explicit; closed. |

## Closed findings and minimal counterexamples

### P0-1: outer measure was not legality

Old shape: `kernel state (actionFiber state) = 1`.

`NonmeasurableFiberLegalityBoundary` uses `Bool` with the bottom measurable
space, `Action _ := Unit`, and a constant Dirac kernel at a bundle based at
`true`. At state `false`:

- `falseFiber_not_measurable` proves the relevant action fiber is not
  measurable;
- `old_mass_one_at_false` proves the old outer-measure equation is `1`;
- `illegalBundle_not_mem_falseFiber` and `not_ae_mem_falseFiber` prove the
  sampled bundle is not actually legal almost surely;
- `no_actionPolicy_with_badKernel` proves the repaired policy structure cannot
  package that kernel.

Repair: the primary legality field at the state, state-history, event-history,
observed-information, realized-action, chance-realization, player-profile, and
replacement-profile layers is now direct membership in the appropriate
almost-everywhere filter. Numerical measure-one recovery is local to measurable
fibers. No global `MeasurableSingletonClass State` was added.

### P0-2: endpoint policies were not complete occurrence strategies

Old risk: the global `GameTree.Strategy` indexes equal endpoint subtree values
identically even when they occur at different paths.

`OccurrenceNonIso` contains two equal-subtree occurrences. An occurrence
strategy chooses different child actions at those histories, while every
lifted endpoint strategy must agree. Repair:

- historical theorems remain valid under explicit
  `GlobalEndpoint...` names;
- the occurrence compiler is root-bound and its strategies index complete
  player history occurrences;
- `Kuhn_exists_occurrencePureSPE` proves standard all-history pure SPE against
  arbitrary occurrence-contingent unilateral deviations.

### P0-3: designated roots were not standard subgames

`DesignatedContinuationSPEBoundary` constructs an entry game with an
off-path incredible threat:

- the initial-only presentation satisfies designated-continuation Nash;
- `rootOnlySubgameSystem` proves that the presentation admits a genuine,
  nonempty lawful system, and the threat satisfies
  `IsPureSubgamePerfectOn` relative to that conservative one-root
  system;
- the off-path continuation has an explicit profitable player-1 deviation;
- a canonical complete system for the same initial-only occurrence
  presentation includes the structurally lawful off-path root independently
  of designation;
- that canonical system is proved not presentation-visible;
- lifting the same threat to the canonical occurrence compiler fails
  `IsPureStandardSubgamePerfect` on the complete all-history system.

Repair: presentation data is named
`IsDesignatedContinuationRoot`; generic data is `IsDeclaredRoot`; one-root
lawfulness is `IsLawfulSubgameRoot`; relative equilibrium is
`IsPureSubgamePerfectOn`; and standard SPE requires a
`CompleteSubgameSystem`. Lawful systems no longer carry a designation field;
`SubgameSystem.IsPresentationVisible` expresses that optional relationship.
The old root and unsuffixed relative-SPE spellings are deprecated
compatibility accessors only.

### P1 findings closed in the same loop

1. `InfoState` documentation no longer claims equivalence with current
   `Observation`; only projection is required.
2. Generic limit equilibrium is named Nash on declared roots, not SPE.
3. The old state-restart behavioral predicate no longer presents itself as
   canonical standard SPE.
4. FOSG serialization exposes declared macro-root Nash, not macro SPE.
5. Strict observed isomorphisms preserve designated roots, structural
   lawfulness, selected lawful systems, and complete systems explicitly;
   generic morphisms preserve declared roots.
6. The root `EconCSLib.lean` aggregate exports the measure-free finite/PMF
   execution layer, the standalone finite `GameTree` and backward-induction
   track, and the exact rational zero-sum chance tree. Infinite paths,
   endpoint-policy equilibrium, occurrence compilers, analytic execution,
   relations, restart, and compilation are explicit opt-ins through their
   focused modules or interface tiers.
7. The fresh-restart aggregate is 39 lines; the implementation is split into
   semantic leaves. The largest leaf is `Certificates.lean` at 1,168 lines,
   followed by `Assembly.lean` at 818 lines. Documentation no longer claims a
   false universal 800-line limit.
8. Four discrete execution/relation implementation files now live under
   `Execution/Discrete/` and `Relations/Discrete/` instead of the semantically
   vague historical `Simulation/` paths. The living audit, module register,
   migration guide, and governed import graph now agree on those filenames
   and on the narrowed root closure.

### P2 historical-document handling

Older audit files still contain superseded names such as macro SPE. They are
retained as historical evidence rather than silently rewritten. The research
index states that only this file is living; current API navigation and status
documents use the repaired names.

## Axiom audit

The temporary audit import executed `#print axioms` on:

- `MeasurableKernelArena.ActionPolicy.ae_mem_actionFiber`;
- `MeasurableKernelArena.ActionPolicy.legal_mass_one`;
- `FiniteImperfectGame.actionAt_same_info`;
- `StochasticGameTree.fairCoinLaw_total`;
- `StochasticGameTree.fairCoin_expected_player0`;
- `ZeroSumChance.GameTree.saddle_bounds`;
- `ZeroSumChance.GameTree.saddle_value`;
- `ExtensiveGame.ObservedGame.init_isLawfulSubgameRoot`;
- `ExtensiveGame.ObservedGame.CompleteSubgameSystem.canonical`;
- `ExtensiveGame.ObservedGame.CompleteSubgameSystem.isRoot_iff_isLawful`;
- `GameTree.Kuhn_exists_occurrencePureSPE`;
- `ExtensiveGame.ObservedGame.IsPureStandardSubgamePerfect.isNashAtInit`;
- `ExtensiveGame.ObservedGame.IsPureStandardSubgamePerfect.toNashOnLawfulRoots`;
- `ExtensiveGame.ObservedGame.Iso.isPureStandardSubgamePerfect_iff`;
- `ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedPathUtility.isFreshRestartStandardSubgamePerfect_iff_isStandardSubgamePerfect_of_compatible`;
- `ExtensiveGame.ObservedChanceGame.isBehavioralNashOnDesignatedContinuationsAtFuel_iff_mixed`;
- `IndexedContinuationGameForm.isNashOnRootsForInfinitePayoff_of_uniformDeviationConvergence`;
- `Examples.AbsentMinded.firstDecision_isLawfulSubgameRoot`;
- `Examples.DesignatedContinuationSPEBoundary.rootOnlyOccurrence_completeSubgameSystem_exists`;
- `Examples.DesignatedContinuationSPEBoundary.rootOnlyOccurrence_canonical_not_presentationVisible`;
- `Examples.DesignatedContinuationSPEBoundary.occurrenceThreat_not_isPureStandardSubgamePerfect`.

`init_isLawfulSubgameRoot` and
both `CompleteSubgameSystem.canonical` and
`CompleteSubgameSystem.isRoot_iff_isLawful` are axiom-free.
`Examples.AbsentMinded.firstDecision_isLawfulSubgameRoot` and the
complete-system existence regression report only `[propext]`; the negative
presentation-visibility regression reports `[propext, Quot.sound]`.
`FiniteImperfectGame.actionAt_same_info` reports
`[propext, Quot.sound]`. The finite PMF calculations, rational zero-sum saddle
theorems, the negative standard-SPE regression, and the remaining
choice-based construction theorems report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No audited theorem depends on `sorryAx` or a project-specific mathematical
axiom. The temporary `/private/tmp/EfgCurrentAxiomAudit.lean` file is not a
repository artifact and is removed after final readback.

## Verification evidence

All commands ran from the repository root against the current worktree.

| Command | Result |
|---|---|
| Targeted lawfulness/SPE/boundary/import builds | passed through the full source and example builds, including all permanent positive, negative, and import-boundary regressions |
| `lake build` | passed, 8,763 jobs |
| `lake build EconCSLib.Examples` | passed, 8,763 jobs, including permanent negative import regressions |
| `python3 scripts/check_efg_governance.py` | passed: 139 registered modules, 19 import-only compatibility paths, root closure 19 EFG / 147 local, and 30 registered `Simulation/` modules |
| `python3 scripts/report_efg_declaration_usage.py --check --output /tmp/efg-declaration-usage.md` | passed: 1,371 registered theorems/lemmas, 377 conservative zero-source-indegree candidates, and no public route-regression leak |
| `python3 scripts/check_lean_placeholders.py EconCSLib` | passed |
| `python3 -m unittest tests/test_check_knowledge_references.py` | 5 tests passed |
| `python3 scripts/check_knowledge_references.py docs/knowledge` | passed |
| `mdblueprint-check docs/knowledge --lean-root .` | 0 errors, 0 warnings |
| `git diff --check` | passed |
| temporary `lake env lean /private/tmp/EfgCurrentAxiomAudit.lean` | passed with fully qualified declaration names; axiom sets recorded above |
| primary-code deprecated-root/SPE-use scan | no matches |
| restart implementation line-count check | 39-line aggregate; leaf counts recorded above |

Warnings printed during full builds are pre-existing Mathlib/API deprecations
and linters outside the semantic findings in this audit; there were no Lean
errors.

## Residual risks and precise nonclaims

No open correctness blocker or high-severity issue was found in the audited
surface. The following are boundaries, not hidden completion claims:

1. A `SubgameSystem` is an explicit caller-selected lawful system. It need not
   enumerate every mathematically possible proper subgame, so only `...On`
   results are available from it. A `CompleteSubgameSystem` certifies exact
   coverage of all `IsLawfulSubgameRoot`s and is required by the standard
   predicates. The canonical complete system exists for every observed game;
   the occurrence compiler also supplies its convenient all-history form for
   finite perfect-information `GameTree`.
2. An arbitrary presentation can declare only the initial continuation.
   Its designated-root results are accurately named designated-root Nash.
   This metadata does not remove structurally lawful roots from standard SPE.
3. A strategy type can be empty in a malformed presentation with an
   uninhabited abstract action at an information state. Predicates taking a
   profile do not fabricate inhabitants, and existence theorems must construct
   profiles under model-specific nonemptiness. The canonical `GameTree`
   occurrence existence theorem is nonvacuous because every decision node has
   a nonempty child type.
4. A raw representation-neutral `ContinuationGameForm` may declare no roots;
   `IsNashOnRoots` is then vacuous by design and its name makes no standard
   subgame or existence claim. Observed presentations and lawful systems
   separately require the initial root.
5. Analytic compilers still require users to prove the stated measurability,
   probability, legality, integrability, and realization fields. The framework
   does not infer these from informal model intent.
6. Fresh-clock restart and absolute-prefix continuation may differ. Their
   transfer requires the explicit compatibility certificate, including
   deviations.
7. Behavioral/mixed Kuhn equivalence is finite, bounded, and
   perfect-recall-dependent. No unconditional infinite or absent-minded
   equivalence is claimed.
8. FOSG serialization is exact at macro boundaries but remains a weak,
   progressing relation rather than a strict history isomorphism.
9. Continuous-time holding kernels, non-explosion, and
   càdlàg/Skorokhod-path results are not implemented.
10. Deprecated compatibility names remain callable during migration. They are
    excluded from primary implementation paths and documented as relative or
    presentation-scoped interfaces. The false-suggesting historical
    `GameTree` SPE theorem aliases were removed rather than preserved.
    Projection-style reads remain source compatible, but Lean cannot alias
    named structure-field syntax; record literals must adopt the documented
    designated/declared field labels.
    `SubgameSystem` literals also now supply the single `lawful` field rather
    than duplicating its two derived proof projections.
11. The dirty worktree prevents commit-local attribution. Reproducibility is
    therefore expressed by commands and declaration names rather than a claim
    that commit `c42e9b0` alone contains these repairs.

## Repair-loop log

| Round | Timestamp / evidence point | State transition |
|---|---|---|
| R1 | 2026-07-29, source/regression phase | Reproduced and repaired nonmeasurable-fiber legality through every policy and realization layer; added permanent negative regression. |
| R2 | 2026-07-29, finite-EFG phase | Separated endpoint/global structural policies from root-bound occurrence strategies; proved occurrence-sensitive Kuhn standard SPE and strict non-isomorphism boundary. |
| R3 | 2026-07-29, solution/API phase | Split designated-root Nash from explicit-system SPE; added initial-only threat regression; corrected observation/information semantics, generic root names, limit/state-restart/FOSG names, and public tiers. |
| R4 | 2026-07-29 00:32 CST, verification phase | Targeted, public, full, examples, knowledge, placeholder, whitespace, static, and axiom checks passed. No blocker/high remained before readback. |
| R5 | 2026-07-29 00:48 CST, readback/red-team phase | Corrected three audit references to real declaration names; added the limit theorem to `#print axioms`; found and repaired remaining designated/declared-root wording in source docs; documented named-record migration; made generic empty-root vacuity explicit; constructed and compiled the nonempty lawful `rootOnlySubgameSystem` and its relative-SPE theorem. |
| R6 | 2026-07-29 00:52 CST, earlier revalidation | Rebuilt the then-five public interface targets, the full library, and all examples after readback; reran placeholder, knowledge, blueprint, whitespace, deprecated-name, current-document, root-terminology, and axiom checks. The later completeness round supersedes this snapshot. |
| R7 | 2026-07-29, completeness red-team phase | Found that a lawful `SubgameSystem` could still be conservative while its unsuffixed predicate was described as standard. Added the designation-independent `IsLawfulSubgameRoot`, exact-coverage `CompleteSubgameSystem`, `...SubgamePerfectOn` versus `...StandardSubgamePerfect` APIs at pure and analytic layers, and strict-isomorphism completeness transport. A second definition attack made the whole-game initial root lawful by convention while retaining singleton information for proper player roots; the absent-minded regression proves both sides of that boundary. |
| R8 | 2026-07-29, import/document phase | Split discrete execution, analytic execution, relations, equilibrium, restart, and compilation tiers; made Restart and Compilation sibling branches; added root-aggregate, equilibrium-tier, and compilation-tier negative import regressions; corrected the endpoint compiler's false perfect-information wording. Final revalidation is recorded in the evidence table. |
| R9 | 2026-07-29 13:53 CST, legacy/model repair phase | Removed the impossible total `Arena.play` chooser and the mass-losing state-based behavior semantics; rewrote stochastic trees around normalized `PMF` laws and occurrence paths; made compact imperfect-information actions explicitly information-indexed; made complete lawful systems canonical and designation-independent; removed misleading structural `GameTree` SPE aliases; and downgraded stale knowledge-node theorem links to honest proof gaps. Full, example, knowledge, placeholder, whitespace, and axiom checks were rerun. |
| R10 | 2026-07-30, physical-layout and root-closeout phase | Moved discrete kernel execution to `Execution/Discrete/` and discrete structural/weak relations to `Relations/Discrete/`; narrowed the root to the finite/PMF and standalone finite-tree tracks; registered every source, compatibility path, facade closure, deprecation, and forbidden root dependency in the executable governance check. |
| R11 | 2026-07-30 10:14 CST, current-state red-team phase | Rechecked quantifier scope, nonvacuity, legality, complete-system standard SPE, occurrence deviations, restart compatibility, and current file ownership. Corrected the living audit's stale root-export sentence and four invalid unqualified example theorem names, then reran the axiom audit with names Lean actually resolves and repeated all current verification gates. |
| R12 | 2026-07-30 16:03 CST, governance cleanup phase | Removed superseded cycle audits, repaired knowledge-node status and declaration alignment, privatized continuation/refinement route regressions with negative import guards, added the lifecycle-aware declaration-usage artifact and CI leak check, updated stale EFG paths and standard-subgame documentation, and repeated all current verification gates. |

Earlier sub-minute wall-clock timestamps were not retained; the source
declarations and command results, rather than reconstructed times, are the
completion evidence.

## Readback attack checklist

The complete audit was reread from the first line and attacked as follows:

- Old-legality falsification: the original audit cited nonexistent shorthand
  names. Source inspection identified and recorded the actual trio
  `old_mass_one_at_false`, `not_ae_mem_falseFiber`, and
  `no_actionPolicy_with_badKernel`. Together they prove both acceptance by the
  old numerical condition and rejection by the repaired structure.
- Root/deviation nonemptiness: the initial-only example originally treated
  presentation designation as if it bounded structural subgames. The readback added
  `rootOnlySubgameSystem`, proved its information laws, and compiled
  `threat_isPureSubgamePerfectOn_rootOnly`. The completeness red-team then
  separated this relative result from standard SPE, proved the omitted
  off-path root structurally lawful, constructed the canonical complete system
  independently of presentation metadata, proved that it is not
  presentation-visible, and showed the threat fails canonical
  `IsPureStandardSubgamePerfect`.
- Occurrence nonvacuity: the audit's placeholder occurrence-strategy name was
  replaced with the real theorem
  `separatingOccurrenceStrategy_distinguishes`. The Kuhn proof was rechecked:
  its unilateral strategy binder ranges over the complete occurrence-game
  `PureStrategy`, not only endpoint lifts.
- “Standard SPE”: source comments for designated roots once used “subgame
  root” in strict isomorphism, chance, continuation, behavioral, finite
  compiler, and measurable-continuation modules. They now say
  presentation-designated or caller-declared roots. Primary solution names now
  reserve `Standard` for complete lawful-root coverage and use `On` for a
  selected system; remaining old names are deprecated relative-scope
  compatibility aliases. The false state-restart behavior API was removed.
- “Exact/equivalence”: strict two-way transports were checked for strategy
  equivalences/surjectivity and evaluator naturality. Information-refinement
  reflection remains fine-to-coarse; reverse results visibly require strategy
  surjectivity. FOSG remains a progressing relational simulation.
- Hidden assumptions: singleton measurability occurs only in numerical
  measure-one recovery and the compatibility constructor; finite/countable,
  decidability, perfect-recall, termination, integrability, and restart
  compatibility premises remain local and are listed in the matrix.
- Vacuity: raw generic continuation forms may declare no roots, and malformed
  presentations may have empty strategy types. These possibilities are now
  explicit residual boundaries. Observed designated and lawful root systems
  contain the initial root; the canonical nontrivial `Fin 2` regressions
  exhibit actual strategies, deviations, and strict payoff comparisons.
- API migration: deprecated projections preserve reads, but Lean cannot alias
  named record-field labels. The public API note now states the required
  record-literal field migration instead of overstating source compatibility.
- Axiom evidence: the uniform-deviation limit-Nash theorem was added to the
  temporary audit. The completion and legacy-model rounds also added the
  complete-system equivalence, standard strict-isomorphism transfer, standard
  restart equivalence, canonical-system visibility boundary, compact
  imperfect-information transport, normalized stochastic-tree calculations,
  and negative standard-SPE theorem.
- Evidence-name resolution: the current round compiled the axiom audit itself,
  rather than trusting names copied from prose. Four example declarations
  required their real `Examples.*` namespace; the living record now contains
  those fully qualified names.

The final public/full/example build was run immediately before this recorded
readback; final static checks were rerun after the documentation updates.

## Next-round action

No correctness blocker or high-severity finding remains. Future work should
remove deprecated compatibility names only in a planned release, and should
add new model-specific lawful systems or convergence theorems only with the
same positive/negative/vacuity evidence discipline.
