# EFG Minimal-Core Structure Audit

**Snapshot:** 2026-08-03 · **Scope:** payoff-free foundations and their
immediate public boundary · **Authority:** current Lean source and source
import graph

## 1. Executive verdict

The mathematical data line remains unchanged:

```text
Arena { State, Action, next }
  -> ControlledGame N { init, mover }
    -> ControlledObservedGame N {
         private/public observations,
         decision information/actions,
         coherence/equivalence laws
       }
```

No payoff, probability, objective, recall, finiteness, root selection, or
solution concept was added to these records. The architecture work in this
snapshot changes declaration ownership, orthogonal adapters, and facade
accuracy, not the mathematical carrier. This three-record line is now frozen:
new semantic fields require a demonstrated representation failure that cannot
be handled by an external certificate, adapter, relation, or compiler.

| Property | Verdict | Source-based reason |
|---|---|---|
| Data-record minimality | Pass | The three records and their fields are unchanged. |
| Literal structural import boundary | Pass, F1 resolved | `Interface.StructuralCore` has the exact five-module EFG/local closure enforced by governance. |
| Infrastructure cohesion | Pass, F2 resolved | Six responsibility leaves separate execution, general well-formedness, subgames, finite certificates, quasistrategies, and recall; their aggregate is a declaration-free canonical facade. |
| Morphism layering | Pass, F7 resolved | Structural, lawful-subgame, and recall transport have separate exact closures; their aggregate is a declaration-free canonical facade. |
| Foundation-facade accuracy | Pass | `Interface.Core` is documented and governed as a Foundation Facade, not as the literal core. |
| Objective/payoff neutrality | Pass through evaluator-relative semantics | Core reaches neither `Execution.Objective` nor `Winning.*` nor payoff-aware `Observed.Game`; `ControlledObservedGame` owns only evaluator-relative continuation equilibrium, while operational standard-SPE definitions remain in concrete execution layers. |
| Probability neutrality | Pass at StructuralCore; bounded PMF is intentional in Core | StructuralCore has no PMF module; Core intentionally imports `StochasticExecution`. |
| Assumption generality | Pass | Finiteness, decidability, recall, termination, measurability, and ambient-state no-chance remain external. Canonical pure execution needs only reachable no-chance. |
| Player-label compatibility | Pass for bijections | `relabelPlayers` reindexes mover, observation, information, actions, presentations, profiles, and lawful/complete subgame systems without changing Arena histories. |
| Representation compatibility | Pass with explicit preservation claims | Compilers and relations retain their existing preservation packages; absence from a package is not inferred. |
| Controlled module-family clarity | Pass, F12 resolved | The complete `Observed.Controlled` hierarchy has one carrier, five semantic owners, nine responsibility owners, two declaration-free facades, and three payoff-aware adapters; flat siblings are forbidden. |
| Current validation health | Source, mathematical, and local branch-history gates pass | Clean aggregate/example builds and semantic/governance checks pass; the rewritten branch and all subsequent changes pass the repository's commit-scope checker. |

There remains no architectural reason to replace `Arena`.

## 2. Exact data core

### 2.1 `Arena`

Owner: `EconCSLib.GameTheory.ExtensiveGame.Basic`.

```lean
structure Arena where
  State  : Type*
  Action : State -> Type*
  next   : (s : State) -> Action s -> State
```

Terminality is derived from an empty action fiber. Reachability, histories,
complete plays, execution laws, and objectives are derived outside the record.
Randomized play places a law over legal actions; it does not change the
deterministic transition carrier.

### 2.2 `ControlledGame N`

Owner: `EconCSLib.GameTheory.ExtensiveGame.Basic`.

```lean
structure ControlledGame (N) extends Arena where
  init  : State
  mover : State -> Option N
```

At a reachable nonterminal state, `some i` identifies a player decision and
`none` is the nature label. Terminal mover normalization is not a record
field; its exact reachable-history certificate is recorded in section 7.

### 2.3 `ControlledObservedGame N`

Owner: `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled`.

The record adds private and public observations, decision information,
information-indexed actions, and the structural laws `observe_public`,
`infoAt_observe`, and `actionEquiv`. It stores no payoff, chance law,
objective, root selection, recall, termination, or finiteness assumption.

`ContinuationRootPresentation G` remains a separate caller-selected
presentation. A declared root is not thereby a standard EFG subgame.

### 2.4 Exact generality boundary

The core is general for turn-based extensive-form games with dependent legal
actions, world-state carriers that may contain cycles or merges, and distinct
occurrence-sensitive histories. It supports both finite and infinite complete
plays. That statement has four intentional limits:

1. `mover : State -> Option N` designates at most one player or nature at a
   state. Simultaneous decisions require a semantics-preserving frontend such
   as the FOSG serializer; they are not silently identified with one ordinary
   EFG move.
2. `next` is deterministic after a legal action. Non-atomic transition laws
   live in `MeasurableKernelArena`; an adapter to an Arena path law must make
   legality and any state/action enlargement explicit.
3. Current `Hom`/`Iso` declarations compare games after choosing the same
   player carrier. A bijective rename is normalized structurally by
   `ControlledObservedGame.relabelPlayers`, with a dependent pure-profile
   equivalence and unchanged Arena/history carrier. Adding, deleting, or
   merging players remains an explicit non-bijective compiler operation.
4. `ControlledObservedGame` deliberately permits unrepresented information
   states and terminal endpoints carrying a player label.
   `AllDecisionInfoRepresented` and `DecisionMoverCoherent` are external
   certificates, so the data record does not confuse a model obligation with
   universal structure.

These are scope boundaries, not hidden hypotheses. A theorem outside this
boundary must add an adapter or a named certificate instead of strengthening
`Arena` globally.

## 3. Exact StructuralCore boundary

Stable facade:
`EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore`.

The facade itself is excluded from both counts. Its exact transitive closure is
**5 EFG / 5 local `EconCSLib` modules**:

1. `EconCSLib.GameTheory.ExtensiveGame.Basic`
2. `EconCSLib.GameTheory.ExtensiveGame.Execution.Reachability`
3. `EconCSLib.GameTheory.ExtensiveGame.Execution.History`
4. `EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay`
5. `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled`

The positive regression
`Examples.ExtensiveGame.StructuralCoreImportBoundary` elaborates
`Arena`, `ControlledGame`, `Arena.History`,
`Arena.CompletePlayFromHistory`, `ControlledObservedGame`,
`ContinuationRootPresentation`, `PureStrategy`, `PureProfile`,
`relabelPlayers`, and `relabelPureProfileEquiv`.

The governance checker compares the complete EFG closure with the exact set
above. Therefore any new source edge to `Execution.Length`,
`StoppedExecution`, `StochasticExecution`, `Objective`, `Winning.*`,
payoff-aware observed games, PMF/path-law or measurable-kernel
implementations, morphisms, equilibrium, simulation/restart, or compilers
fails the check. This is stronger than a finite list of comment-based negative
name tests.

## 4. Interface.Core is the Foundation Facade

Stable facade: `EconCSLib.GameTheory.ExtensiveGame.Interface.Core`.

The facade itself is excluded from both counts. Its exact transitive closure is
**14 EFG / 14 local `EconCSLib` modules**:

1. `EconCSLib.GameTheory.ExtensiveGame.Basic`
2. `EconCSLib.GameTheory.ExtensiveGame.Execution.Reachability`
3. `EconCSLib.GameTheory.ExtensiveGame.Execution.History`
4. `EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay`
5. `EconCSLib.GameTheory.ExtensiveGame.Execution.Length`
6. `EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution`
7. `EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution`
8. `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled`
9. `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Core`
10. `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.WellFormed`
11. `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Subgame`
12. `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Finite`
13. `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Quasi`
14. `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Recall`

Core contains the five StructuralCore implementation modules but does not
import the `Interface.StructuralCore` facade module itself. Its stable
responsibility includes structural length/well-foundedness, bounded
terminal-aware deterministic execution, bounded PMF execution, represented
information and mover coherence, finite-EFG packages, quasistrategies, recall,
and lawful subgame systems.

Core does not promise every accidental transitive declaration. Governance now
rejects `Execution.Objective` and every `Winning.*` module in its closure.
It also remains subject to the payoff-free reverse-dependency rules, which
exclude payoff-aware observed games and their compatibility adapters,
equilibrium, and simulation.

## 5. Controlled.Infrastructure physical split

`Observed.Controlled.Infrastructure` is a canonical aggregate facade
containing only imports and a module docstring. It re-exports the six leaves
and `Winning.Basic`, while implementation modules import the narrowest defining
leaf.

| Defining leaf | Authoritative responsibility |
|---|---|
| `Controlled.Infrastructure.Core` | no-chance mover helpers, pure-profile history execution, and pure-strategy complete-play compatibility |
| `Controlled.Infrastructure.WellFormed` | `DecisionInfoWitness`, represented information, mover coherence, terminal normalization on reachable histories, and inhabited strategy/profile consequences |
| `Controlled.Infrastructure.Subgame` | occurrence-sensitive continuation, `IsLawfulSubgameRoot`, `SubgameSystem`, `CompleteSubgameSystem`, and their bijective player-relabel transport |
| `Controlled.Infrastructure.Finite` | uniform history-length, finite reachable-action/information assumptions, `FiniteEFGHypotheses`, and its well-foundedness/termination consequences |
| `Controlled.Infrastructure.Quasi` | nonempty action permissions, quasistrategies, refinement, pure embedding, and play compatibility |
| `Controlled.Infrastructure.Recall` | personal decisions, own-decision histories, perfect/signal/public recall, no-absent-mindedness, and recall certificates |
| `Winning.Basic` | winning conditions, pure robust winning, and the winning-dependent `HasWinningQuasiStrategy` predicate |

Every declaration retains its original namespace and full declaration name.
No definition is copied between leaves. `Finite` and `Recall` both import the
minimal `WellFormed` owner. Neither imports the other, and `Recall` therefore
reaches no `Finite`, `Execution.Length`, or controlled execution module.

The exact source-graph change for `Controlled.Infrastructure.Recall` is:

| Snapshot | Exact EFG closure, excluding `Recall` itself |
|---|---|
| Before | `Basic`, `Execution.{Reachability,History,CompletePlay,Length}`, `Observed.Controlled`, `Controlled.Infrastructure.Finite` |
| After | `Basic`, `Execution.{Reachability,History,CompletePlay}`, `Observed.Controlled`, `Controlled.Infrastructure.WellFormed` |

The closure shrank from **7 to 6 EFG/local modules**. The governance checker
compares the complete post-refactor set exactly; the
`RecallImportBoundary` regression independently confirms that
`FiniteEFGHypotheses` and `Arena.HasLengthBoundFrom` are not name-resolvable.

Before the split, six implementation/facade modules directly imported the
broad aggregate: `Controlled.Morphism`, `Winning.Determinacy`,
`Interface.Core`, `Controlled.Compat.Infrastructure`, `Observed.Quasi`,
and `FiniteUnfolding`. That broad aggregate edge count is now **0**.
Each imports only the leaf or leaves it actually uses. In particular:

- `Controlled.Morphism.Subgame` and `Controlled.Morphism.Recall` import only
  their corresponding infrastructure leaf and the morphism core;
- `Interface.Core` imports all promised leaves directly, but not the
  aggregate facade;
- `FiniteUnfolding` imports `Finite` and its actual winning dependency
  directly;
- `Winning.Determinacy` imports execution Core, Finite, Recall, and
  `Winning.Basic`;
- compatibility adapters remain downstream of payoff-free owners.

The payoff-free Core closure consequently lost its former
`Controlled.Infrastructure -> Winning.Basic -> Execution.Objective` edge.

### 5.1 `Controlled.Morphism` declaration split

The former 1,883-line canonical file had three genuine declaration layers:

| Defining leaf | Declaration families |
|---|---|
| `Controlled.Morphism.Core` | `Hom`; `InformationRefinement`; strict `Iso`; carrier/history/action/strategy maps; external root-presentation comparison; identity/composition/inverse; and Iso unit/associativity laws |
| `Controlled.Morphism.Subgame` | continuation reachability, `map_isContinuationOf`, `mapLawfulSubgameRoot`, `mapSubgameSystem`, and `mapCompleteSubgameSystem` |
| `Controlled.Morphism.Recall` | personal-decision and own-decision-history transport, signal/public-signal transport, and classic/private/public recall preservation/reflection |

An extra Iso or Fiber leaf was not introduced: the inverse/cast calculus is
used directly to construct `Iso.symm` and remains cohesive with the structural
carrier. `Controlled.Morphism` is a 16-line declaration-free canonical
aggregate facade, and `Controlled.Compat.Morphism` remains the separate
payoff-aware adapter.

The exact post-refactor EFG closures, excluding each entry itself, are:

| Entry | EFG/local closure | Forbidden higher leaves absent |
|---|---:|---|
| `Controlled.Morphism.Core` | 8 / 8 | `Controlled.Infrastructure.{Subgame,Recall,Finite}`, `Controlled.Morphism.{Subgame,Recall}`, and `Execution.Length` |
| `Controlled.Morphism.Subgame` | 10 / 10 | both recall leaves, `Finite`, and `Execution.Length` |
| `Controlled.Morphism.Recall` | 11 / 11 | both subgame leaves, `Finite`, and `Execution.Length` |
| aggregate facade | 14 / 14 | re-exports all three leaves by design |

Before the split, `Controlled.Morphism` had a 12-module closure containing
`Controlled.Infrastructure.{Subgame,Recall,Finite}` and `Execution.Length`.
The aggregate facade has a 14-module closure because three
declaration owners replace one and `WellFormed` replaces `Finite`/`Length`;
the useful structural leaf is the materially smaller 8-module boundary.

Internal imports are now narrow: `Controlled.Compat.Morphism`, `Controlled.Law`,
and `Observed.Refinement.Structural` use `Core`; `FiniteUnfolding` uses the
`Subgame` and `Recall` leaves; the relations facade imports all three
deliberately; and `Controlled.Law.Discrete` dropped an unused morphism import.
No internal Lean source imports either controlled aggregate facade.
Governance checks the exact leaf closures, exact facade imports,
declaration-free status, and the absence of an in-scope import cycle.

## 6. Dependency direction and payoff-aware adapters

The governed direction remains:

```text
payoff-free core
  <- projection / adapter
    <- payoff-aware or legacy implementation
```

The complete closures of every new payoff-free leaf are checked against the
same reverse-dependency exclusions as the older payoff-free owners.
StructuralCore is additionally checked against its exact closure.

This snapshot does not claim that every legacy payoff-aware API has migrated.
Payoff-aware `ObservedGame` carriers and adapters remain supported.
`Observed.WellFormed` still owns legacy payoff-aware finite-certificate
spellings alongside the payoff-free owners, while `Observed.Quasi`,
`SignalRecall`, `PerfectRecall`, and the controlled `.Compat` adapter modules
provide downstream payoff-aware projections. These files contain declarations
and are not import-only lifecycle compatibility wrappers. The completed work
removes reverse imports and mixed physical ownership; it does not delete those
payoff-aware surfaces.

Lawful-subgame semantics no longer have two mathematical owners.
`ObservedGame.IsContinuationOf`, `IsLawfulSubgameRoot`, `SubgameSystem`, and
`CompleteSubgameSystem` are reducible compatibility names for the corresponding
definitions on `G.toControlledObservedGame`. Their legacy namespace helpers
delegate to the controlled owner. Likewise, the payoff-aware
`ObservedGame.Iso` subgame transport definitions delegate to
`e.toControlledIso`; they do not repeat the information-set proof.
An `ObservedGame.RootPresentation` has a lossless coercion to the controlled
root presentation, so established dot notation such as
`system.IsVisibleIn roots` remains source-compatible even though the system's
mathematical owner changed.
`ObservedGame.ofControlledObservedGame` supplies the converse compatibility
direction: any state-payoff interpretation can be attached without rebuilding
the observation carrier, erase-after-attach is definitional, and reattaching
an observed game's existing payoff recovers the original record.

## 7. Terminal mover semantics

`DecisionMoverCoherent` quantifies over `G.base.History`, hence over
complete legal histories reachable from `G.base.init`, not every ambient
state in `G.base.State`.

The theorem
`decisionMoverCoherent_iff_terminal_mover_eq_none_on_histories` proves that
this certificate is equivalent to saying every reachable terminal complete
history has mover `none`. Thus the existing certificate already supplies
the relevant normalization without a duplicate well-formedness predicate.

An unreachable terminal Arena state may still carry `some i`. This is not an
outstanding semantic obligation: `Basic` specifies that terminal mover labels
are ignored, because the action fiber is empty. The reachable-history
certificate is available when a compiler or theorem wants a normalized
presentation. Strengthening the data record globally would reject
observationally irrelevant ambient encodings without improving play
semantics.

## 8. Observation fidelity

Lean proves the structural guarantees stored in
`ControlledObservedGame`:

- `observe_public`: private observations refine public observations;
- `infoAt_observe`: decision information projects to the current private
  observation;
- `actionEquiv`: an information action is exactly a represented history's
  concrete legal action.

External certificates record additional model obligations:
`AllDecisionInfoRepresented`, `DecisionMoverCoherent`, and classic,
private-signal, or public recall certificates.

There is no ungrounded global `ObservationFaithful` predicate. Fidelity and
no-leak claims remain compiler-specific and must compare the compiled
observation with a defined source-frontend semantics. The existing FOSG
semantics continues to hide partial actions; this audit does not promote that
fact into a universal record field.

## 9. Preservation and compiler theorem boundary

The following capabilities already exist and are not gaps:

- the preservation matrix and `StrictCompilerPreservation` /
  `WeakCompilerPreservation`;
- payoff-free `ControlledObservedGame.Hom`, `Iso`, and
  `InformationRefinement`;
- FOSG weak serialization;
- event/state/action path bridges;
- separation of continuation-root presentation from lawful subgames;
- the common `CompletePathLawSemantics`;
- discrete and analytic complete-path adapters.

Preservation strength remains axis-specific. A theorem about histories does
not silently prove information, chance, law, objective, deviation, recall,
root, termination, or equilibrium preservation.

The generic preservation boundary is payoff-free and explicit.
`isEvaluatorContinuationEquilibriumAt_iff_of_surjective` gives abstract
evaluator-relative equilibrium equivalence. It deliberately makes no claim
that its evaluator is generated by legal execution from a root-local strategy.
A short-lived generic execution certificate was removed after audit showed
that every evaluator semantics could satisfy it by taking continuation
strategies to be whole strategies, restriction to be the identity, execution
to be the evaluator, and legality to be `True`. Such a certificate did not
separate operational EFG semantics from an arbitrary normal-form evaluator.

Operational standard SPE therefore remains owned by concrete execution modes,
including pure standard SPE in `Observed.SPE`. A future generic standard-SPE
interface must first supply canonical root-local strategies, a compatible
lift/update operation for local deviations, canonical legal complete
plays or path laws, and locality strong enough to recover the concrete
definitions. The explicit FOSG limitations therefore remain:

1. declared continuation roots are not automatically standard EFG subgames;
2. the principal transfer result is finite-horizon behavioral Nash transfer;
3. the serializer does not yet provide complete lawful-root coverage,
   termination-certified whole-continuation outcome compatibility, and the
   target-deviation coverage needed by a future operational theorem.

In particular, the serializer relation connects augmented source macro
histories to target macro boundaries. A target
`CompleteSubgameSystem` ranges over every lawful target history, including any
lawful micro-step root; coverage by a source macro root is therefore an
additional theorem premise, not a consequence of the current relation.
No serializer-specific placeholder or falsely unconditional flagship theorem
was added for these compiler obligations.

`ObservedGame.ContinuationSemantics` is a payoff-aware abbreviation
to the controlled carrier. Its compatibility theorem permits source and target
`ObservedGame`s with different state-payoff types, because neither state
payoff participates in the evaluator, external utility square, strategy
coverage, or lawful-root coverage. A logical or path-objective client can use
the controlled theorem directly without inventing a dummy state-payoff type.

The serializer's game value is now literally root-free:
`FOSG.Sequentialization.observedChanceGameCore G D rootPayoff` has no
declared-root argument. `rootPresentation` attaches
`sourceDeclaredRoot` separately. The established
`observedChanceGame G D rootPayoff sourceDeclaredRoot` spelling remains a
definitionally equal compatibility wrapper, with
`observedChanceGame_eq_core` and the discrete-compilation import regression
checking the old and new surfaces. This removes the former phantom argument
without changing the serialized game, root semantics, or downstream types.

## 10. Semantic contract and lifecycle closeout

The hard migration preserved the carrier line while tightening external
contracts:

- `ControlledGame.NoChanceOnHistories` quantifies only over legal histories
  from `init`; global `NoChance` implies it. Pure execution, total pure
  continuation/SPE, winning, and determinacy use the reachable certificate.
  `Examples.ExtensiveGame.ReachableNoChance` proves an ambient unreachable
  nonterminal nature state can violate global no-chance while canonical pure
  execution and the total continuation game form still elaborate.
- `PureStrategyAvailabilityCertificate` packages represented decision
  information plus mover coherence, while
  `ReachablePureStrategyModelCertificate` adds reachable no-chance. No
  finiteness, probability, payoff, recall, or termination field was added.
- `BoundedHistoryLawFamily` is raw PMF data.
  `CertifiedBehavioralExecutionLaw` adds normalization, legal reachable
  support, terminal absorption, and equality with the concrete behavioral
  executor. Execution-facing finite unfolding uses the certified projection.
- `HistoryTransformLawEquivalentAt` is the generic transform relation.
  `TerminalHistoryLawEquivalentAt` has a terminal-history-subtype codomain.
  `CompletePathLawSemantics` remains a family of lawful per-root marginals and
  does not by itself supply a common causal process; operational,
  restart/conditioning, and coherence claims require separate certificates.
- signal/public recall is explicitly event-clock recall.
  `SignalTraceBuilder` permits `Option Signal`, including silent events; the
  always-emitting builder recovers the event-clock trace, with no claimed
  equivalence for arbitrary silent traces.

All 19 registered compatibility wrappers were deleted after the four
historical broad-import boundary consumers and the wrapper chain were removed.
The declaration-free `Observed.Morphism.Fiber` forwarding path and the
comment-only `Foundation.Player` shell were also removed. The canonical
`Controlled.Infrastructure` and `Controlled.Morphism` aggregate facades remain
because they have explicit navigation responsibilities, exact import sets,
module documentation, and no declarations.

Governance now scans the full Lean source tree for zero-byte,
comment/namespace-only, and import-only files. Import-only modules must appear
in the explicit canonical or temporary-compatibility registry; the current
inventory is 20 canonical façades/aggregates and zero temporary compatibility
paths. Removed paths may not be recreated or imported.

## 11. Module census

The governed in-scope register now contains **163 modules**:

| Status | Modules |
|---|---:|
| Canonical | 86 |
| Frontend | 13 |
| Historical | 7 |
| Compatibility | 0 |
| Experimental | 0 |
| Internal | 57 |
| **Total** | **163** |

The controlled orthogonalization added defining responsibility owners, then
the pre-stability lifecycle closeout removed redirect-only paths without
moving implementation back into aggregates.

## 12. Findings

### F1 — Literal structural import boundary

**Priority:** high · **Status:** resolved

Acceptance evidence:

- `Interface.StructuralCore` exists;
- its exact closure is 5 EFG / 5 local modules;
- the positive import regression builds; and
- source-graph governance rejects every extra EFG module in its closure.

### F2 — Split Controlled.Infrastructure by responsibility

**Priority:** medium · **Status:** resolved

Acceptance evidence:

- declarations are physically owned by six responsibility leaves;
- the compatibility aggregate contains no declaration;
- the six former broad implementation/facade import edges are gone; and
- Core no longer reaches Objective/Winning through infrastructure; and
- Recall's exact closure contains neither `Finite` nor `Execution.Length`.

### F3 — Keep compatibility adapters one-way

**Priority:** high, continuous · **Status:** satisfied in this snapshot

Every new payoff-free leaf is covered by the reverse-dependency governance
check. Legacy payoff-aware APIs remain downstream and are not declared fully
migrated.

### F4 — Require preservation claims to name their strength

**Priority:** high, continuous · **Status:** satisfied at the framework level

The preservation matrix remains authoritative. Compiler-specific fidelity,
standard-subgame coverage, deviation coverage, and SPE transfer require named
theorems.

### F5 — Ambient terminal normalization

**Priority:** low · **Status:** resolved as a non-requirement

Reachable complete histories are covered by
`DecisionMoverCoherent` and its equivalence theorem. No global condition is
imposed on unreachable ambient states because terminal mover labels are
semantically ignored. Clients needing a canonical serialized presentation use
the reachable certificate rather than strengthening `ControlledGame`.

### F6 — General observation fidelity and FOSG standard SPE

**Priority:** model/compiler specific · **Status:** minimal-core framework
resolved; serializer theorem track separate

Only source-relative fidelity statements are meaningful. The generic
evaluator-relative equivalence theorem states its game-form assumptions
explicitly, but it is not a standard-SPE theorem. FOSG declared roots and
finite-horizon Nash transfer do not establish lawful-root, canonical
total-execution, and deviation-coverage premises for a future operational
standard-SPE interface. Those premises cannot be inferred from macro-boundary
simulation alone and are not part of minimal-core completion.

### F7 — Split Controlled.Morphism by semantic layer

**Priority:** medium · **Status:** resolved

Acceptance evidence:

- structural, lawful-subgame, and recall declarations have separate owners;
- their exact closures are 8 / 8, 10 / 10, and 11 / 11;
- the old broad path is deleted after consumers migrated;
- the canonical aggregate remains import-only with exact leaf imports;
- internal consumers import only the leaves they use; and
- governance rejects cross-leaf leaks and import cycles.

### F8 — Separate FOSG game construction from root selection

**Priority:** medium · **Status:** resolved

Acceptance evidence:

- `observedChanceGameCore` has no root-predicate parameter;
- `rootPresentation` is the only non-compatibility constructor in the pair
  whose result depends on `sourceDeclaredRoot`;
- the old root-parameterized spelling remains definitionally equal to the
  root-free value; and
- the discrete compilation boundary checks both entry points and the equality
  theorem.

### F9 — Move generic evaluator-relative continuation semantics below state payoffs

**Priority:** high · **Status:** resolved

Acceptance evidence:

- `ControlledObservedGame.ContinuationSemantics` owns the strategy, horizon,
  outcome, and complete-history evaluator data;
- its Nash-on-presentation and evaluator-relative continuation equilibrium use
  only payoff-free lawful-subgame systems;
- no generic operational standard-SPE name is exported: the attempted
  certificate was constructible for every arbitrary evaluator and was removed
  before API stability;
- source and target games in the evaluator-relative theorem carry no payoff
  parameter;
- `check_efg_governance.py` treats `Controlled.Semantics` as a payoff-free
  boundary and rejects any future closure edge to `ObservedGame`,
  payoff-aware adapters, equilibrium implementations, or simulations;
- `ObservedGame.ContinuationSemantics` is a payoff-aware abbreviation, and
  its transfer wrapper allows different source and target payoff types;
- `ObservedGame.ofControlledObservedGame` and its two round-trip theorems make
  payoff attachment and erasure a checked two-way adapter rather than a
  one-way projection;
- `Interface.Equilibrium.Discrete` exports both the controlled owner and the
  state-payoff compatibility spelling of evaluator-relative semantics, with an
  import-boundary regression checking name visibility;
- `Examples.ExtensiveGame.ReusableSemantics` constructs the measure-valued
  semantics first on `ControlledObservedGame` and derives the payoff-aware
  spelling only through projection.

Generic operational standard SPE is intentionally deferred until a
non-vacuous common execution interface exists. Concrete pure, behavioral, and
analytic equilibrium layers remain responsible for their own execution
semantics meanwhile.

### F10 — Do not call classical backward selection executable

**Priority:** medium · **Status:** resolved as a specification correction

`FiniteTwoPlayerHypotheses.isTwoPlayerDetermined` returns a pure
winning-strategy witness, but `backwardWinner`, `backwardAction`, and
`backwardStrategy` are noncomputable and use classical choice. Its source
docstring now calls it a classical existence theorem rather than a
constructive/executable extraction result. The proposition and proof are
unchanged.

### F11 — Support bijective player relabeling without enlarging the core

**Priority:** medium · **Status:** resolved

Acceptance evidence:

- `ControlledObservedGame.relabelPlayers` changes only the player index along
  an equivalence and leaves the Arena, initial state, and history carrier
  definitionally unchanged;
- mover labels, observations, information states, and dependent action fibers
  are reindexed coherently;
- `relabelPureProfileEquiv` supplies dependent profile transport;
- root presentations reuse the same history predicate;
- `isLawfulSubgameRoot_relabelPlayers_iff` proves both preservation and
  reflection, and selected/complete subgame systems transport with it; and
- the payoff-aware `ObservedGame.relabelPlayers` adapter reindexes endpoint
  payoff coordinates by the same equivalence and exposes its own pure-profile
  equivalence;
- StructuralCore/Core import regressions ensure the relabel API remains
  available without pulling in payoff, probability, or higher solution
  layers.

### F12 — Consolidate the `Observed.Controlled` module hierarchy

**Priority:** medium · **Status:** resolved

There is no duplicate declaration owner or old/new namespace collision. Before
the EFG module paths became stable, the implementation was hard-migrated into
one physical hierarchy:

- `Controlled` is the canonical carrier;
- five law/semantics modules are canonical semantic owners;
- nine infrastructure/morphism leaves are canonical responsibility owners;
- `Controlled.Infrastructure` and `Controlled.Morphism` are declaration-free
  canonical aggregate facades; and
- the three `Controlled.Compat.*` modules are downstream payoff-aware adapters
  declaring only under `ObservedGame` or `ObservedChanceGame`.

The complete map and import selection guide live in
[`efg-controlled-api.md`](efg-controlled-api.md). Governance fixes all twenty
modules, rejects a new flat sibling such as `Observed.ControlledFoo`, and
rejects role/lifecycle mismatches, adapter import changes, adapters reopening a
payoff-free namespace, or canonical modules reaching an adapter.
`ControlledApiImportBoundary` jointly imports all public roles and
checks that canonical and payoff-aware declarations coexist under their
intended mathematical namespaces. Former flat paths are absent; no forwarding
stubs remain.

## 13. Validation and environment health

The final source snapshot was checked from the repository root. The commands
and counts below are the results of this worktree, not inherited CI claims.

| Check | Result | Evidence |
|---|---|---|
| Stable library | Pass | `lake build`: 8,639 jobs. |
| Opt-in examples and regressions | Pass | `lake build EconCSLib.Examples`: 8,809 jobs, including the reachable-no-chance and import-boundary regressions. |
| Discrete equilibrium facade | Pass | Evaluator-relative transfer elaborates through `Interface.Equilibrium.Discrete`; concrete pure standard SPE remains available from its operational owner. |
| EFG governance | Pass | 163 registered modules, 0 temporary compatibility paths, root closure 36 / 163, Simulation 29, and Controlled hierarchy 20 = 1 carrier / 5 semantic owners / 9 responsibility owners / 2 facades / 3 adapters. The source scan reports 0 zero-byte modules, 0 comment/namespace-only modules, and exactly 20 registered canonical import-only aggregates. |
| Lean placeholders | Pass | `check_lean_placeholders.py EconCSLib` reports no forbidden placeholder. |
| Knowledge checks | Pass | Reference unit tests, reference scan, and `mdblueprint-check` all pass with 0 errors and 0 warnings. |
| Declaration lifecycle report | Pass, triage remains | 1,690 theorems/lemmas across 163 modules; 481 conservative zero-source-indegree candidates split into 68 evidenced endpoints, 263 unexplained Canonical/Frontend endpoints under a no-growth ceiling, 136 Internal/private review items, and 14 Historical/lifecycle review items. None is an automatic deletion candidate. |
| Axiom spot audit | Pass | The event-clock recall bridge is axiom-free. The concrete reachable-no-chance regression uses `propext`; evaluator-relative transfer uses `propext` and `Quot.sound`; terminal-history selection and finite `GameTree` standard-SPE existence additionally use `Classical.choice`. No audited result depends on `sorryAx`. |
| EFG warning scan | Pass | Filtered replay of both successful builds reports no warning originating under `GameTheory/ExtensiveGame` or `Examples/ExtensiveGame`. |
| Git/source integrity | Pass | `git diff --check` passes; final status is reported separately at handoff. |

The builds replay warnings from non-EFG source files. Those warnings are
repository-wide maintenance debt rather than evidence against the EFG
semantic changes, but the repository as a whole is not warning-clean.

These checks provide machine-checked evidence for source elaboration, the
axiom surface, placeholder policy, module boundaries, and the listed formal
semantic properties. They are not a metamathematically complete certification
of every intended model meaning. Remote-host CI remains a separate external
check after publication.

## 14. Audit conclusion

The data records were already minimal. The source architecture now exposes
that fact through a genuinely narrow stable facade and a physical
responsibility split for both infrastructure and morphism transport.
`Interface.Core` remains useful under the accurate Foundation
Facade name, while governance prevents the former Objective/Winning and
Recall-to-finiteness leaks from returning. Evaluator-relative equilibrium
transfer now lives on the payoff-free controlled carrier, while operational
standard-SPE semantics remain in concrete execution layers; and
the payoff-aware lawful-subgame and Iso surfaces delegate to that single
owner. State-payoff attachment/erasure is two-way, and bijective player
renaming transports dependent profiles and complete lawful systems without
changing Arena histories. The audit still records payoff-aware adapters and
compiler-specific observation-fidelity/FOSG theorem tracks,
without treating ambient terminal normalization as a core requirement or
claiming that an existing serializer discharges compiler-specific premises.
The validation table records only commands actually run for this worktree.
