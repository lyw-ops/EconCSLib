# EFG Architecture Governance

This document is the authoritative lifecycle and placement policy for
EconCSLib's extensive-form-game implementation.  Mathematical declarations and
their proofs remain authoritative in Lean; public navigation is defined here,
in [`efg-public-api.md`](efg-public-api.md), and in the complete module register
[`efg-module-status.md`](efg-module-status.md).

The initial snapshot was the complete worktree on 2026-07-29 and was updated
after the root and physical-layout closeout on 2026-07-30. It includes
staged, unstaged, and untracked EFG work.  The audit did not infer architecture
from HEAD alone and did not alter the index.

## Verdict and canonical semantic line

The current architecture is logically sound.  Its canonical semantic line is:

```text
 Foundation / Math.Probability.PMF
               │
               ▼
 Arena + Reachability + typed History       representation-neutral GameForm
               │                              │
              ▼                              │
           CompletePlay                       │
               │                              │
               └──────────────┬───────────────┘
                              ▼
           ControlledGame / ControlledObservedGame
                              │
                 ┌────────────┼──────────────┐
                 ▼            ▼              ▼
          Objective/Winning  structural   lawful path
                             relations    probability
                                            │
                                 ┌──────────┴──────────┐
                                 ▼                     ▼
                         discrete PMF adapter   analytic adapter
                                 └──────────┬──────────┘
                                            ▼
                         payoff/equilibrium compatibility
                              ▼
                          ┌────┴─────┐
                          ▼          ▼
                       Restart   Compilation
```

This is a logical ownership diagram, not a claim that every source file forms
one literal import chain.  In particular:

- `Arena`, reachability, typed histories, measure-free complete plays, and
  payoff-free observed control form the exact five-module StructuralCore.
- structural termination, finite/subgame/recall certificates, and bounded
  deterministic/PMF execution are the broader `Interface.Core` Foundation
  Facade.
- history-sensitive terminal and path outcomes are exposed by the opt-in
  `Interface.Objective` facade without probability or equilibrium.
- `ControlledObservedGame` is the minimal payoff-free carrier of controlled
  dynamics and information. `ObservedGame` and `ObservedChanceGame` are
  payoff-aware/discrete compatibility extensions, not dependencies of the
  payoff-free spine.
- finite PMF execution, infinite discrete path execution, and non-atomic
  analytic execution are distinct layers.
- Restart extends analytic equilibrium.  Discrete Compilation extends discrete
  equilibrium.  They are sibling public branches and neither imports the other.

Specialized representations remain inputs or algorithm languages:

```text
GameTree ───────────────────────────────┐
StochasticGameTree ────────────────────┤
FiniteImperfectGame ───────────────────┼─ compiler / proved realization
FOSG ──────────────────────────────────┤                │
ZeroSumChance.GameTree ─ specialized ──┘                ▼
                                            ObservedGame /
                                            ObservedChanceGame /
                                            GameForm
```

`GameTree` endpoint projection and occurrence projection are both useful, but
the endpoint map is not injective when equal subtree values recur.  It is an
information-forgetting relation, not an isomorphism.  `ZeroSumChance.GameTree`
retains independent value as an exact `ℚ` algorithm; the presence of
`ObservedChanceGame` is not a reason to remove it.

### Recorded physical-layout deviations

The source does not perfectly mirror the diagram:

1. `Simulation/` contains analytic execution, presentation assembly, outcomes,
   continuation, and restart implementation. Its Internal leaves are grouped
   below `Kernel/`, `Presentation/`, `Equilibrium/`, `Continuation/`, and
   `Restart/`; discrete execution and relations live separately under
   `Execution/Discrete` and `Relations/Discrete`.
2. `Strategy` is a valid state-indexed Arena policy, but is not equivalent to
   information-indexed `ObservedGame.PureStrategy`.
3. `Subgame.subgameAt` changes a state root; a presentation-designated
   continuation and a lawful `ObservedGame.SubgameSystem` make strictly
   different claims. The representation-neutral `Arena.Reachable` relation and
   initial-state specialization now live separately in canonical
   `Execution.Reachability`, so typed histories do not import `Subgame`.
4. The endpoint `GameTree` NE/SPE/strategic-form route remains available by
   explicit import but left the root closure on 2026-07-30; occurrence-sensitive
   observed strategies are canonical for standard EFG SPE.
5. Several implementation modules exceed 800 lines.  Their audit below shows
   that most large proof chains are highly coupled and are not made safer by a
   mechanical split.
6. The former mixed-responsibility
   `Observed.ControlledInfrastructure` path is now an import-only compatibility
   aggregate. Its declarations are physically owned by `Core`, `WellFormed`,
   `Subgame`, `Finite`, `Quasi`, and `Recall` leaves; winning-dependent
   quasistrategy predicates live in `Winning.Basic`. `Recall` has an exact
   six-module closure and reaches neither `Finite` nor `Execution.Length`.
7. The former monolithic `Observed.ControlledMorphism` path is also an
   import-only compatibility aggregate. Structural transport is owned by
   `ControlledMorphism.Core`, lawful-subgame transport by `.Subgame`, and
   recall transport by `.Recall`; their exact EFG/local closures are 8 / 8,
   10 / 10, and 11 / 11.
8. FOSG sequentialization keeps its observed chance-game value independent of
   continuation-root selection. `observedChanceGameCore` is root-free,
   `rootPresentation` owns the source-root predicate, and the established
   root-parameterized `observedChanceGame` name is a definitionally equal
   compatibility wrapper.

These deviations are governed below. Physical path changes are limited to
Internal modules whose importers are inside this worktree. Public clients use
facades, while the one established restart compatibility path is retained.

## Lifecycle classes

### Canonical

Canonical modules own reusable semantics.  General Nash, SPE, continuation,
and representation-transfer theory should be stated here unless its statement
genuinely mentions a frontend-specific object.  Canonical declarations may be
implemented in non-public leaves, but consumers import the granular facade.

An incompatible canonical change requires:

1. a mathematically equivalent or explicitly narrower replacement;
2. an API migration note;
3. a positive import regression for the replacement;
4. a negative boundary regression when dependency closure changes; and
5. a major release when source compatibility cannot be preserved.

### Frontend

A frontend may own:

- syntax, validation, structural recursion, and executable algorithms natural
  to that representation;
- representation-specific correctness theorems;
- a compiler, realization, refinement, or simulation into the canonical layer;
  and
- exact algorithmic results that would become less useful if forced through a
  more general carrier.

A frontend must not acquire a second general-purpose Nash/SPE/continuation
hierarchy merely because the theorem can be restated there.  New general
theory first targets observed EFGs or game forms and is transferred through the
proved boundary. A direct dependency on a Historical module is forbidden
unless the exact importer/imported pair is registered as a
semantic-preservation bridge with a written reason.

### Historical

Historical declarations are retained because they are mathematically valid
and may have downstream users, not because they are the preferred semantics.
They receive correctness fixes, documentation, and preservation regressions
only.  They do not receive parallel general theory.

Do not attach `@[deprecated replacement]` when the replacement changes the
strategy space, information partition, root scope, or deviation quantifier.
In particular, endpoint and occurrence `GameTree` policies are not
interchangeable, state re-rooting is not a lawful subgame certificate, and a
designated continuation is not a complete subgame system.

### Compatibility

A compatibility module:

- preserves its import path;
- contains only imports and a module docstring;
- names the granular or canonical replacement;
- must not define new implementation; and
- may be removed only in a major release after internal users are zero and the
  migration window is documented.

The broad `Interface.Execution.Discrete`, `Relations`, `Equilibrium`,
`Compilation`, and `SimulationFramework` imports preserve their historical
closures.  New code imports a granular facade and may not rely on accidental
transitive declarations.

### Internal and experimental

Internal modules implement a stable facade.  Their proof helpers are
name-resolvable through Lean imports but are not individually frozen.  They
may be reorganized only when the change measurably lowers dependency or
navigation cost.  A known downstream path receives a thin wrapper. Direct
Historical imports require the same exact, reasoned pairwise exception as
Frontend imports; directory-level and wildcard exceptions are not permitted.

Experimental modules are opt-in and must say what evidence would promote them.
No in-scope module currently needs the Experimental classification; unfinished
mathematical targets belong in the knowledge blueprint rather than in
placeholder Lean declarations.

## Placement rules for new work

Place a new declaration at the lowest layer that can state it honestly:

| Declaration depends on | Home |
|---|---|
| players, profiles, order, or probability only | `Foundation/` or `Math/` |
| strategy/outcome maps without histories | `GameForm/` |
| raw state-dependent dynamics | `ExtensiveGame/Basic` |
| finite transition reachability | `Execution/Reachability` |
| typed action occurrences | `Execution/History` |
| measure-free complete plays or structural termination | `Execution/CompletePlay` or `Execution/Length` |
| terminal-history or complete-path objectives | `Execution/Objective`, exposed by `Interface.Objective` |
| observations, information, chance, or lawful roots | `Observed/`; controlled execution/well-formedness/subgame/finite/quasi/recall infrastructure and structural/subgame/recall morphisms use the matching focused leaf |
| finite/infinite/analytic execution | the corresponding execution implementation, exposed by its facade |
| strict/refinement/coupling/weak representation relation | relation implementation, exposed by `Relations.Discrete` |
| general pure/behavioral/mixed Nash, SPE, recall, or realization | observed/game-form equilibrium layer |
| fresh-clock versus absolute-prefix compatibility | restart implementation, exposed only by `Interface.Restart` |
| syntax-specific recursion or exact solver | the frontend |
| preservation from a frontend | `Compiler/` or that frontend's serializer |

New modules are not added to `EconCSLib.lean` merely because they compile.  A
root import requires broad stable utility, a bounded dependency closure, an
explicit lifecycle decision, and root-boundary regression coverage.  Analytic,
restart, compiler, internal, experimental, `Examples`, and `OpenProblem`
modules are opt-in by default.

### When a new representation is allowed

A new representation is justified only if at least one of the following is
structural rather than cosmetic:

- it admits an algorithm unavailable on the canonical carrier;
- it records data the current carriers cannot express without loss;
- it materially improves executable finite models;
- it is an established external language whose faithful translation matters;
  or
- it isolates a stronger assumption package that yields a useful proof method.

The proposal must identify the information, action-occurrence, chance,
termination, and root semantics that differ from existing frontends.
Directory symmetry, shorter record literals, or a second spelling of an
existing carrier is insufficient.

### When a compiler is required

A frontend must provide a compiler, exact realization, refinement, or
simulation before adding theory that is intended to be representation
independent.  The boundary states exactly what is preserved:

- histories or only endpoints;
- action occurrences or only action values;
- information and public observations;
- chance-law pushforwards or couplings;
- payoff laws or expectations;
- unilateral deviations; and
- designated, selected lawful, or complete lawful roots.

Non-bijective endpoint/occurrence maps are never called isomorphisms.  A weak
serializer that inserts administrative states proves macro-boundary laws
instead of claiming one-step strict equivalence.

### When parallel theory is forbidden

Do not add a frontend-specific general Nash/SPE/continuation theorem when:

1. its statement can be made on `ObservedGame`, `ObservedChanceGame`, or
   `GameForm`;
2. the frontend already has a preservation boundary; and
3. the only remaining proof is transport.

An exception is permitted for an executable solver or structural induction
theorem whose algorithmic content is native to the frontend.  Its result must
still be related to canonical semantics before it is described as a general
EFG theorem.

## Legacy API decisions

| Path or family | Decision | Replacement or distinction |
|---|---|---|
| `BehaviorStrategy` | Keep as import-only wrapper; never restore removed declarations | `ObservedGame.BehavioralStrategy`, normalized chance kernels, and `Finite`/`EqD` |
| `Play` | Keep as import-only wrapper | terminal-aware `Execution.StoppedExecution` / `Finite` |
| `ExtensiveGame.Probability.*` | Keep as import-only wrappers | `Math.Probability.PMF.*` |
| broad Interface aggregates | Keep through the current major version | smallest granular facade |
| split implementation aggregates | Keep import-only; implementation modules now import defining leaves directly | corresponding subdirectory leaves; downstream users prefer facades |
| `Observed.ControlledInfrastructure` | Keep as import-only compatibility aggregate | defining `ControlledInfrastructure.*` leaf; winning predicates are in `Winning.Basic` |
| `Observed.ControlledMorphism` | Keep as import-only compatibility aggregate | `ControlledMorphism.Core`, `.Subgame`, or `.Recall` according to the declarations used |
| endpoint `GameTree` NE/SPE/strategic form | Historical, retained, stopped from general expansion | occurrence compiler for canonical standard SPE; no false deprecation |
| `GameTree.toObservedGame` | Historical endpoint compiler, retained for old policy semantics | occurrence compiler when paths must be distinguished |
| state-based `Strategy` | Historical but semantically valid | observed pure strategy is information-indexed and not definitionally equivalent |
| `Subgame.subgameAt` / `reachableSubgameAt` | Historical state re-root/restriction tools | not synonymous with designated roots or lawful/complete subgame systems |
| `FiniteImperfectGame` | Supported frontend, not a theorem layer | compile via `ObservedCompiler` or `ObservedChanceCompiler` |
| `actionAt_same_info_label` | Exact deprecated alias may remain | `actionAt_same_info` since 2026-07-29 |
| `ZeroSumChance.GameTree` | Supported specialized frontend | exact rational algorithm has no equivalent replacement |
| `GameForm.LimitSPE` | Historical path with a correct, explicit convergence theorem | indexed continuation Nash on declared roots; it does not certify standard SPE |

Canonical implementation files were audited for compatibility imports.  The
governance closeout replaced direct aggregate imports with defining leaves in
the continuation, behavioral-refinement, deferred-sampling,
Kuhn-conditioning, FOSG-sequentialization, and restart-certificate chains.
Compatibility aggregates remain intentionally imported only by other
Compatibility paths and explicit boundary regressions. Historical imports from
Canonical, Frontend, or Internal modules are rejected unless an exact
importer/imported pair with a reason is present in the governance checker.
The current exceptions are the occurrence-to-endpoint compiler preservation
bridge and the endpoint-policy results used by `FiniteArenaExtraction` and
`Zermelo`.

## Root aggregate lifecycle

The root was narrowed on 2026-07-30 and re-audited on 2026-08-01. Its current
closure is 37 EFG modules and 165 local `EconCSLib` modules. It exposes
measure-free complete plays, structural termination, reusable finite-EFG
certificates, finite/PMF execution, finite `GameTree` syntax and
backward-induction values, but no infinite path law,
historical endpoint-policy equilibrium, Arena extraction, Zermelo theorem,
analytic execution, Restart, FOSG, compiler, Historical, or Compatibility
module.

The governed direct-import closure budgets are recalculated from the current
source graph:

| Entry | EFG modules / all local modules |
|---|---:|
| `EconCSLib` | 37 / 165 |
| `Interface.StructuralCore` | 5 / 5 |
| `Interface.Core` | 14 / 14 |
| `Interface.Objective` | 32 / 37 |
| `Interface.Winning` | 35 / 40 |
| `Interface.Winning.Stochastic` | 50 / 57 |
| `Interface.Execution.Finite` | 33 / 40 |
| `Interface.Execution.Infinite` | 38 / 45 |
| `Interface.Execution.Analytic` | 58 / 66 |
| `Interface.Relations.Discrete` | 39 / 46 |
| `Interface.Equilibrium.Discrete` | 66 / 82 |
| `Interface.Equilibrium.Analytic` | 96 / 113 |
| `Interface.Restart` | 104 / 121 |
| `Interface.Compilation.Discrete` | 87 / 105 |

| Path | Class | Root decision | Explicit import for opt-in use |
|---|---|---|---|
| `Interface.Execution.Finite` | stable finite/PMF execution | retained as the root EFG facade | same path |
| `Interface.Objective` | stable measure-free objective semantics | opt-in; terminal/path objectives are not required by every root client | same path |
| `GameTree` | stable specialized frontend | retained | same path |
| `BackwardInduction` | stable specialized frontend algorithm | retained | same path |
| `ZeroSumGameTreeWithChance` | stable specialized exact solver | retained | same path |
| `Interface.Execution.Discrete` | compatibility aggregate | removed from root | `Interface.Execution.Infinite` for path laws, or the old aggregate |
| `GameTreeSPE` | historical endpoint semantics | removed from root | `EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE` |
| `GameTreeNE` | historical endpoint semantics | removed from root | `EconCSLib.GameTheory.ExtensiveGame.GameTreeNE` |
| `GameTreeStrategicForm` | historical endpoint semantics | removed from root | explicit module import |
| `FiniteArenaExtraction` | stable but niche frontend bridge | removed from root | explicit module import |
| `Zermelo` | stable specialized theorem over historical endpoint policies | removed from root | explicit module import |

The migration includes explicit internal imports for existing examples and
positive/negative `RootImportBoundary` regressions. Historical declarations
remain available and receive no false `deprecated` replacement.

## Simulation responsibility matrix

All 30 modules currently under `Simulation/` have one primary responsibility
below.
“Partial” means the name is historically broader or narrower than the current
role; it is not evidence that the declarations are mathematically mixed.

| Module below `Simulation` | Category | Unique primary responsibility | Name fit | Dependency direction | Physical decision |
|---|---|---|---|---|---|
| `Kernel/DiscreteBridge` | analytic execution | exact full-path coherence of discrete and analytic executors | Yes | discrete + analytic execution | Grouped |
| `Kernel/Arena` | analytic execution | non-atomic one-step transition carrier | Yes | Mathlib kernels → analytic execution | Grouped |
| `Kernel/Execution` | analytic execution | legal terminal-aware action and state-step kernels | Yes | arena → policy execution | Grouped |
| `Kernel/Endpoint` | analytic execution | finite endpoint iteration and discrete recovery | Yes | one-step execution → endpoints | Grouped |
| `Kernel/StatePath` | analytic execution | stationary infinite state paths | Yes | endpoint/step → Ionescu–Tulcea path | Grouped |
| `Kernel/HistoryPath` | analytic execution | state-prefix-dependent infinite execution | Yes | path core → history policies | Grouped |
| `Kernel/EventPath` | analytic execution | joint state/action event paths and state projection | Yes | history path → event path | Grouped |
| `Kernel/ObservedEvent` | observed analytic presentation | fixed-information event policies and pullback | Yes | event execution → information presentation | Grouped |
| `Kernel/RealizedInformation` | observed analytic presentation | abstract actions with history-dependent realization | Yes | observed event → realization | Grouped |
| `Presentation/Chance/KernelBridge` | observed analytic presentation | complete-history PMF observed profile to analytic kernel | Yes | observed finite → analytic | Grouped |
| `Presentation/Chance/Realized` | observed analytic presentation | explicit realization certificate | Yes | realization → observed presentation | Grouped |
| `Presentation/Chance/Countable` | observed analytic presentation | automatic countable-discrete certificate | Yes | countability → presentation | Grouped |
| `Presentation/Chance/MeasurableHistory` | observed analytic presentation | explicit measurable history carrier | Yes | observed structure → analytic model | Grouped |
| `Presentation/Chance/Measurable` | observed analytic presentation | uncountable reachable presentation certificate | Yes | measurable history → presentation | Grouped |
| `Presentation/Kernel/Core` | observed analytic presentation | non-atomic player/chance kernel presentation | Yes | realized information → kernel profile | Grouped |
| `Presentation/Chance/ProfileAssembly` | profile assembly | exact PMF-to-kernel assembly seam | Yes | old presentation → assembly | Grouped |
| `Presentation/Kernel/ProfileAssembly` | profile assembly | measurable player kernels and deviations | Yes | presentation → profile/deviation | Grouped |
| `Equilibrium/Outcome` | outcome/equilibrium | path utility, Nash, termination, and payoff limits | Yes | assembly → economic outcome | Grouped |
| `Continuation/Path` | continuation/conditioning | raw absolute-prefix continuation path | Yes | event path → continuation path | Grouped |
| `Continuation/Conditioning` | continuation/conditioning | raw positive-atom and a.e. conditional bridge | Yes | continuation → conditioning | Grouped |
| `Continuation/Observed` | continuation/conditioning | observed absolute/fresh continuation and equilibrium predicates | Partial: also owns equilibrium adapters | outcome + path → continuation equilibrium | Grouped |
| `Continuation/ObservedConditioning` | continuation/conditioning | observed lift of conditional compatibility | Yes | raw conditioning → observed outcome | Grouped |
| `Restart/Core` | restart | root marker normalization and finite splice | Yes | continuation → restart core | Grouped |
| `Restart/Trajectory` | restart | spliced full and finite trajectory laws | Yes | restart core → trajectory | Grouped |
| `Restart/Certificates` | restart | raw step/path/action certificates | Yes | trajectory → certificates | Grouped |
| `Restart/Observed` | restart | observed profile to state-law compatibility | Yes | certificates → semantic target | Grouped |
| `Restart/Assembly` | restart | baseline and all-deviation compatibility | Yes | observed certificate → deviations | Grouped |
| `Restart/Equilibrium` | restart | canonical compatibility-to-equilibrium route | Yes | assembly → equilibrium | Grouped |
| `Restart/Factorization` | restart | statistic/rebase sufficient constructors | Yes | raw certificates → constructors | Grouped |
| `ObservedMeasurableKernelRestartCompatibility` | compatibility aggregate | preserve the complete old restart import | Yes | imports final restart leaf | Thin wrapper |

### Implemented physical-layout changes

Four Internal modules with unambiguous ownership were moved without
compatibility wrappers because their old implementation paths were never
promised public API:

| Old path below `Simulation` | New implementation path | Reason |
|---|---|---|
| `KernelArena` | `Execution/Discrete/KernelArena` | owns the finite PMF transition carrier |
| `KernelTrajectory` | `Execution/Discrete/KernelTrajectory` | owns finite PMF execution and trace laws |
| `Morphism` | `Relations/Discrete/Morphism` | owns deterministic Arena relations |
| `KernelWeakSimulation` | `Relations/Discrete/KernelWeakSimulation` | owns probabilistic weak/stuttering relations |

The 29 Internal analytic modules were subsequently regrouped below
`Kernel/`, `Presentation/`, `Equilibrium/`, `Continuation/`, and `Restart/`.
This was a path-only cleanup: declaration names and public facades did not
change. Repeated semantic prefixes now live in directory names instead of
every filename. The established
`ObservedMeasurableKernelRestartCompatibility` import remains as the sole
long compatibility filename.

## Large-file audit

Declaration counts are top-level declaration-family counts used for
maintenance triage, not API cardinalities.

| Module | Lines / declarations | Main responsibility | Semantic layers crossed | Cohesion | Repeated transport/index work | Existing bundle | Candidate split | Risk | Decision |
|---|---:|---|---|---|---|---|---|---|---|
| `Compiler.GameTreeObserved` | 836 / 57 | endpoint compiler and exact legacy-policy bridges | frontend → execution → game form | High: one preservation chain | Moderate dependent-history transport | game-form isomorphism and termination package | construction / operational / strategic bridge | High; occurrence compiler imports it | Keep |
| `Compiler.GameTreeOccurrenceObserved` | 1214 / 56 | occurrence compiler, refinement bridge, and finite SPE | frontend → observed relation → equilibrium | High around one compiler | High history/action transports | complete system and refinement objects | core / endpoint bridge / Kuhn | High; public compiler names and long proof chain | Keep; future trigger at next independent compiler theorem |
| `Execution.InfiniteTrajectory` | 917 / 43 | path law, stopping, payoff convergence | infinite execution → outcome limit | High around one path law | Moderate time indices | probability-measure and stopping packages | path construction / payoff convergence | Medium-high; shared filtration and measurability lemmas | Keep |
| `Observed.BehaviorMorphism` | 847 / 28 | behavioral strategy/execution/equilibrium transfer | relation → execution → bounded equilibrium | High around strict isomorphism | High casts through dependent action fibers | strategy equivalence and continuation iso | strategy transport / law transfer / Nash | Medium; split could lower imports but duplicates transport context | Queue only |
| `Observed.Continuation` | 1001 / 36 | pure and behavioral continuation adapters | pure + behavioral equilibrium adapters | Medium-high; two parallel halves | Moderate casts | continuation morphism/simulation/iso bundles | pure / behavioral leaves plus aggregate | Medium; useful only if clients need one half independently | Queue on measured import demand |
| `Observed.Kuhn` | 866 / 41 | finite hypotheses, behavioral-to-mixed, realization | finite probability → strategy → equilibrium | High proof progression | Moderate table/index transport | hypothesis structures and realization records | hypotheses / plan sampling / realization | Medium-high; wrappers share theorem names | Keep |
| `Observed.PerfectRecall` | 934 / 33 | personal-decision recall and iso transfer | information structure → relation transfer | High | High dependent-list transport | `RecallCertificate` | structure / iso transfer | Medium-high; certificate equivalence links halves | Keep |
| `Observed.ControlledMorphism` (former monolith) | 1883 / layered declaration families | payoff-free structural, lawful-subgame, and recall transport | controlled structure → subgames/recall | Three separable layers | High dependent casts in the structural base | `Hom`, `InformationRefinement`, and `Iso` | `Core` / `Subgame` / `Recall` leaves plus aggregate | Low after preserving names and old import path | **Split implemented**; exact closures 8 / 8, 10 / 10, and 11 / 11 |
| `Observed.SPE` | 923 / 34 | total pure semantics and lawful/complete SPE | termination → root systems → equilibrium transfer | High | High history/root transport | terminating-on and complete-system packages | termination / equilibrium / iso transfer | High; cyclic import risk with morphism/refinement | Keep |
| `Kernel.EventPath` | 1119 / 60 | event paths, policies, state projection | analytic execution + projection bridge | High | High coordinate/index arithmetic | `EventHistoryActionPolicy` and path measures | event core / policy path / projections | High; Ionescu–Tulcea proof chain | Keep |
| `Presentation.Chance.Countable` | 1347 / 59 | reachable countability and automatic analytic presentation | types/instances → realization → profile compiler | High | High dependent tags and casts | `presentation`, `measurablePresentation`, kernel adapter | carriers / realization / profile adapters | High; scoped instances cross every section | Keep |
| `Continuation.Observed` | 1108 / 58 | absolute/fresh continuation and bounded/terminal equilibrium | path → outcome → two utility regimes | Medium-high | High clock/prefix arithmetic | named bounded and terminal predicate families | path adapter / bounded utility / terminal utility | High; same continuation identities feed both regimes | Keep |
| `Equilibrium.Outcome` | 1028 / 45 | path utility, Nash, termination, convergence | assembly → outcome → limit payoff | High | Moderate measure transports | bounded and terminal extension structures | utility/Nash / terminal convergence | Medium-high; shared integrability lemmas | Queue only if another outcome family appears |
| `Presentation.Kernel.ProfileAssembly` | 987 / 36 | measurable profile/deviation assembly | presentation → roles → deviations | High | High tagged dependent transport | `ProfileAssembly` and `PlayerStrategy` | roles/core / deviations / adapters | High; measurable instances are cross-cutting | Keep |
| `Restart.Assembly` | 818 / 56 | lift every raw certificate to all deviations | restart certificates → semantic compatibility | High theorem matrix | Low casts, high repeated route plumbing | deviation-compatible predicates | split by certificate family | Medium; would worsen route navigation | Keep |
| `Restart.Certificates` | 1168 / 30 | prove equivalence/implication chain among raw certificates | step kernels → finite prefixes → full paths | Very high | Very high splice/index arithmetic | named certificate propositions | implication families | High; one induction chain | Keep |

The current worktree contains the high-value, dependency-ordered splits for
controlled morphisms, continuation game forms, observed
morphisms/refinements, deferred sampling, Kuhn conditioning, FOSG
sequentialization, and Restart. The controlled-morphism split was driven by
three independently useful dependency closures, not line count alone. No
additional low-risk/high-benefit split was identified; the remaining
mechanical line-count splits would either cut a single induction/transport
chain or add wrappers without reducing facade closure.

## Maintenance queue and stop conditions

1. Revisit `Observed.Continuation` only if a real client can avoid a material
   behavioral or pure dependency by importing one half.
2. Revisit `BehaviorMorphism` only after its dependent-cast helpers can be
   packaged without duplicating proof state.
3. Revisit analytic outcome/continuation files when a second independent
   outcome or continuation family makes the current cohesion false.
4. Revisit the two large compiler files during a planned compiler API release,
   not during unrelated theorem work.
5. Retain Restart `Certificates` and `Assembly` while their implication graphs
   remain single proof chains; line count alone is not a split trigger.
6. Consider further physical `Simulation/` moves only when ownership is as
   unambiguous as the discrete execution/relation moves or an import-closure
   measurement demonstrates a reduction. Navigation aesthetics alone do not
   pass the gate.
7. Keep historical root removals covered by explicit-import examples and
   negative root guards.

This queue is intentionally part of the governance document rather than a new
collection of one-off audit files.

## Enforceable invariants

The source-graph portion of this policy is checked in CI with:

```bash
python3 scripts/check_efg_governance.py
```

The check makes closure changes deliberate: a facade or root dependency change
must update its boundary regression and the audited count in this policy,
rather than remaining an invisible transitive import. Review and CI maintain:

- canonical implementation modules do not import compatibility wrappers;
- `Interface.StructuralCore` has exactly the five structural EFG dependencies
  and `Interface.Core` cannot regain Objective/Winning;
- every payoff-free `ControlledInfrastructure.*` leaf obeys the existing
  reverse-dependency prohibition;
- `ControlledInfrastructure.Recall` has its exact six-module closure and
  cannot regain `Finite` or `Execution.Length`;
- `ControlledMorphism.{Core,Subgame,Recall}` retain their exact 8 / 8,
  10 / 10, and 11 / 11 closures without cross-layer leakage;
- `Observed.ControlledInfrastructure` and `Observed.ControlledMorphism`
  remain import-only with exact direct leaf imports, while internal consumers
  import defining leaves;
- compatibility aggregates are imported only by other compatibility paths or
  intentional compatibility-boundary regressions;
- the governed EFG/GameForm/PMF source graph is acyclic;
- Canonical, Frontend, and Internal modules do not directly import Historical
  modules except for exact, reasoned importer/imported allowlist pairs;
- `Execution.History` cannot import `Subgame`, and `StochasticGameTree` cannot
  import `GameTreeSPE`;
- `Core`, `Finite`, `Infinite`, `Analytic`, relations, equilibrium, Restart,
  and Compilation keep their documented negative sentinels;
- root does not gain Historical or Compatibility paths, infinite path,
  analytic, restart, FOSG, or compiler modules transitively;
- Restart and Compilation remain sibling branches;
- `Math/Probability/PMF` imports no game theory;
- `Examples` and `OpenProblem` do not enter stable aggregates;
- all compatibility modules appear in the module register and name a
  replacement;
- every `@[deprecated]` EFG declaration appears in
  [`efg-api-migration.md`](efg-api-migration.md);
- no ordinary `sorry` or `admit` appears below `EconCSLib/`; and
- no compatibility, historical, or internal status is inferred solely from a
  filename: the source responsibility is checked.
