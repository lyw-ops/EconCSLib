# EFG Downstream Migration

This note records the source-level changes made while converging the EFG
public facade. No theorem or mathematical construction was deleted; the main
compatibility impact is that a few clients must add a narrower explicit import
or update pre-release record-field labels.

## Import migration

| Former dependency | Required import now |
|---|---|
| occurrence-sensitive `GameTree` compiler obtained from `import EconCSLib` | `import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete` |
| bounded deterministic, observed behavioral, or PMF-kernel execution obtained from `Interface.Execution.Discrete` | `Interface.Execution.Finite` avoids infinite path measures; the old import remains valid |
| infinite discrete `Arena.pathLaw`, almost-sure termination, or payoff convergence | `Interface.Execution.Infinite`; the old `Interface.Execution.Discrete` import remains valid |
| measurable-kernel execution obtained transitively | `Interface.Execution.Analytic` |
| strict representation morphisms, information refinements, PMF couplings, or weak simulations | `Interface.Relations.Discrete` |
| bounded pure/behavioral/mixed Nash, termination, or finite Kuhn transfer | `Interface.Equilibrium.Discrete` |
| measurable path utility, constructive kernel Nash, absolute-prefix continuation, or conditioning | `Interface.Equilibrium.Analytic` |
| fresh-clock restart declarations | `Interface.Restart` |
| finite observed-EFG compilers or PMF FOSG serialization | `Interface.Compilation.Discrete` |
| both restart and compiler branches from one legacy import | `Interface.SimulationFramework` (compatibility-only) |

The root aggregate exports finite/PMF execution and the standalone finite
`GameTree`/backward-induction and exact zero-sum chance-tree tracks. Infinite
discrete paths, historical endpoint-policy equilibrium, Arena extraction,
Zermelo, and the observed-EFG reference compilers now require explicit
imports.

No source edit is required merely because a caller already imports
`Interface.Execution.Discrete`, `Interface.Relations`,
`Interface.Equilibrium`, or `Interface.Compilation`: those paths retain their
former declaration closures as supported compatibility aggregates. Switching
to a new granular path is an opt-in dependency reduction. That earlier facade
split moved no declaration; the stricter path-law record and payoff-free
ownership changes below are the separate intentional source migration.

### Controlled infrastructure and morphism import paths

Before EFG API stability, the flat paths

```lean
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledInfrastructure
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledMorphism
```

were removed. Their canonical aggregate replacements are:

```lean
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism
```

No forwarding stubs remain at the flat paths. Every declaration keeps its
namespace, parameters, and full declaration name; only imports change. New
internal code should import the narrow owner:

| Need | Narrow defining import |
|---|---|
| represented information or mover coherence | `Observed.Controlled.Infrastructure.WellFormed` |
| pure controlled execution | `Observed.Controlled.Infrastructure.Core` |
| lawful roots and subgame systems | `Observed.Controlled.Infrastructure.Subgame` |
| finite EFG hypotheses | `Observed.Controlled.Infrastructure.Finite` |
| quasistrategies | `Observed.Controlled.Infrastructure.Quasi` |
| classic/private/public recall | `Observed.Controlled.Infrastructure.Recall` |
| structural Hom/Iso, information refinement, or strategy transport | `Observed.Controlled.Morphism.Core` |
| lawful-subgame transport | `Observed.Controlled.Morphism.Subgame` |
| recall transport | `Observed.Controlled.Morphism.Recall` |

This is an import-ownership migration, not a declaration rename.
`Controlled.Infrastructure.Recall` no longer exposes finite or length
declarations transitively, and `Controlled.Morphism.Core` no longer exposes
subgame or recall transport transitively. Callers that intentionally relied
on broad visibility can import the corresponding canonical aggregate facade.

The complete hierarchy and the distinction between a declaration-free
aggregate facade and a payoff-aware module under `.Compat` are catalogued in
[`efg-controlled-api.md`](efg-controlled-api.md).

### FOSG root-free compiler value

The serialized observed chance-game value does not depend on a continuation
root predicate. New code that needs only the compiled game should use:

```lean
FOSG.Sequentialization.observedChanceGameCore G D rootPayoff
```

Attach caller-selected roots separately with
`FOSG.Sequentialization.rootPresentation G D rootPayoff sourceDeclaredRoot`.
The established
`observedChanceGame G D rootPayoff sourceDeclaredRoot` spelling remains a
definitionally equal compatibility wrapper, so existing calls and
dependent types continue to elaborate unchanged.

## Law-semantics migration

The pre-release `CompletePathLawSemantics` record is intentionally stricter.
Direct record literals must now provide:

```lean
{ Strategy := ...
  pathLaw := ...
  pathLaw_isProbability := ...
  pathLaw_ae_legal := ... }
```

`pathLaw_isProbability` rules out the zero measure and
`pathLaw_ae_legal` uses the canonical initial-coordinate, legal-step, and
terminal-absorption predicate. Local-kernel agreement is no longer inferred
or stored in the maximum carrier; prove `RealizesExecution` or
`ExecutionCoherent` separately. Any former downstream
`ObservedChanceGame.CompletePathLawSemantics` spelling is an abbreviation to
this controlled carrier through `Observed/PathLawEquivalence.lean`.

The maximum carrier has no PMF/countability/chance tag. Use
`Controlled.Law.DiscretePath` for discrete behavioral execution and
`Controlled.Law.Analytic` for an assembled measurable-kernel execution. The
latter requires an explicit almost-sure canonical-legality proof.

Payoff-free declarations now live in `Controlled.Infrastructure`,
`Controlled.Morphism`, `Controlled.Law.Discrete`, `Controlled.Law`,
`Winning.Basic`, and `Winning.Determinacy`. Existing payoff-aware projection
lemmas are available from the corresponding `Controlled.Compat.*` modules.
Clients that imported an implementation file directly may need to add that
explicit adapter import; public `Interface.*` facades provide their documented
surface.

## Record-field migration

The following pre-release field labels were semantically too strong. Update
named record literals as follows:

| Structure family | Old field | Current field |
|---|---|---|
| `ContinuationGameForm`, `IndexedContinuationGameForm` | `IsSubgameRoot` | `IsDeclaredRoot` |
| their `Hom`, `Iso`, and relation structures | `map_subgameRoot` | `map_declaredRoot` |
| their root-coverage predicates | `SubgameRootSurjective`, `SubgameRootReflecting` | `DeclaredRootSurjective`, `DeclaredRootReflecting` |
| former `ObservedGame` root fields | `IsDesignatedContinuationRoot`, `init_isDesignatedContinuationRoot` | external `RootPresentation.IsRoot`, `RootPresentation.init_isRoot` |
| observed isomorphism/refinement structures | embedded `map_designatedContinuationRoot` metadata | external root-presentation correspondence predicates |
| `FOSG.WeakSerialization` | target `ObservedGame.IsDesignatedContinuationRoot` | explicit `targetRoots : RootPresentation` and `targetRoots.IsRoot` |

For example:

```lean
-- before
{ Strategy := Strategy
  Root := Root
  IsSubgameRoot := roots
  Outcome := Outcome
  outcome := outcome }

-- now
{ Strategy := Strategy
  Root := Root
  IsDeclaredRoot := roots
  Outcome := Outcome
  outcome := outcome }
```

An observed presentation and its analysis roots now use separate values:

```lean
def observed : ObservedGame N U :=
  { base := base
    -- observation and information fields omitted
  }

def roots : observed.RootPresentation :=
  { IsRoot := selected
    init_isRoot := init_mem }
```

Changing `roots` no longer changes observed-game identity. The former embedded
designated-root declaration and its all-history compatibility adapter were
removed: no value can recover arbitrary root metadata formerly stored in a
record value, and widening it would be unsound. Root-aware Nash, continuation,
and realization APIs accept a `RootPresentation` explicitly.

## `SubgameSystem` literals

`ObservedGame.SubgameSystem` separates selection from structural lawfulness.
Construct it with exactly:

```lean
{ IsRoot := roots
  init_isRoot := init_mem
  lawful := by
    intro root hroot
    exact
      { root_information_singleton := by
          -- prove the proper-root singleton condition
          ...
        information_closed := by
          -- prove information-set closure after the root
          ... } }
```

`root_information_singleton` and `information_closed` remain derived
accessors on a completed `SubgameSystem`. Presentation designation is not a
field; prove `SubgameSystem.IsVisibleIn roots` separately when needed.
Use `CompleteSubgameSystem` only when the selected roots cover every
`IsLawfulSubgameRoot`.

## Solution-concept names

The old `IsSPEForPayoff` and unqualified `Is...SubgamePerfect` spellings were
not retained. Choose the name that states the actual root scope:

- `IsNashOnRoots...` or `IsNashOnPresentationAt ... roots` for explicitly
  selected presentation roots;
- `Is...SubgamePerfectOn ... system` for one explicit lawful system; or
- `Is...StandardSubgamePerfect ... completeSystem` for coverage of every
  structurally lawful root.

A caller-declared or presentation-designated root predicate is not, by itself,
a standard-subgame certificate. Compatibility aliases with former designated
names use the broad all-history view only; new code must pass roots explicitly.

## Declaration deprecations

The finite imperfect-information frontend has one exact declaration alias:

| Deprecated declaration | Replacement | Since | Semantics |
|---|---|---|---|
| `FiniteImperfectGame.actionAt_same_info_label` | `FiniteImperfectGame.actionAt_same_info` | 2026-07-29 | Identical transport-aware information-consistency statement |
| `PathOutcomeFromHistory.continueAt` | `PathOutcomeFromHistory.rebaseTailAt` | 2026-07-31 | Same absolute-tail rebasing operation; root objectives now use `PathOutcome.afterHistory` |
| `WinningConditionFrom.continueAt` | `WinningConditionFrom.rebaseTailAt` | 2026-07-31 | Same absolute-tail rebasing operation; root objectives now use `WinningCondition.afterHistory` |
| `WinningConditionFrom.mem_continueAt_iff` | `WinningConditionFrom.mem_rebaseTailAt_iff` | 2026-07-31 | Same membership equivalence |
| `ObservedGame.HasWinningStrategy` | `ObservedGame.HasPathwiseWinningStrategy` | 2026-07-31 | Same pathwise robust predicate; profile-based winning is now separately named |
| `ObservedGame.WinningStrategies` | `ObservedGame.PathwiseWinningStrategies` | 2026-07-31 | Same bundled pathwise strategies |
| `ObservedGame.IsDetermined` | `ObservedGame.HasSomePathwiseWinningStrategy` | 2026-07-31 | Same generic existential; standard determinacy naming is reserved for the two-player disjunction |
| `ObservedGame.isDetermined_of_hasWinningStrategy` | `ObservedGame.hasSomePathwiseWinningStrategy_of_hasPathwiseWinningStrategy` | 2026-07-31 | Same existential packaging result |
| `ObservedGame.isDetermined_iff_isTwoPlayerDetermined` | `ObservedGame.hasSomePathwiseWinningStrategy_iff_isTwoPlayerDetermined` | 2026-07-31 | Same two-player equivalence |
| `ObservedGame.not_both_haveWinningStrategy` | `ObservedGame.not_both_havePathwiseWinningStrategy` | 2026-07-31 | Same exclusivity theorem with explicit pathwise semantics |
| `ObservedGame.GeneralStrategy` | `ObservedGame.DiscreteGeneralStrategy` | 2026-07-31 | Same countably supported `PMF` carrier; the new name does not imply analytic generality |
| `ObservedGame.GeneralProfile` | `ObservedGame.DiscreteGeneralProfile` | 2026-07-31 | Same playerwise discrete carrier |
| `BehavioralStrategy.toGeneral` | `BehavioralStrategy.toDiscreteGeneral` | 2026-07-31 | Same Dirac embedding |
| `BehavioralProfile.toGeneral` | `BehavioralProfile.toDiscreteGeneral` | 2026-07-31 | Same componentwise Dirac embedding |
| former embedded designated-root predicate | `roots.IsRoot` | 2026-08-01 | Removed rather than widened; callers must supply the original root set explicitly |
| former zero-argument root-presentation adapter | explicit `ObservedGame.RootPresentation` value | 2026-08-01 | Removed because no lossless default can recover the former embedded metadata |
| `ObservedGame.IsPresentationVisible` | `ObservedGame.SubgameSystem.IsVisibleIn roots` | 2026-07-31 | Presentation visibility now names the explicit external root presentation |
| `ContinuationSemantics.toIndexedGameForm` | `ContinuationSemantics.toIndexedGameFormOnPresentation roots` | 2026-07-31 | Explicit external root presentation |
| `ContinuationSemantics.toIndexedGameForm_outcome` | `ContinuationSemantics.toIndexedGameFormOnPresentation_outcome roots` | 2026-07-31 | Same outcome computation on an explicit root presentation |
| `ContinuationSemantics.IsNashOnDesignatedContinuationsAt` | `ContinuationSemantics.IsNashOnPresentationAt roots` | 2026-07-31 | Explicit external root presentation |
| `ContinuationSemantics.isNashOnDesignatedContinuationsAt_iff` | `ContinuationSemantics.isNashOnPresentationAt_iff roots` | 2026-07-31 | Same Nash characterization on an explicit root presentation |
| `IsPureNashOnDesignatedContinuationsAtFuel` | `IsPureNashOnRootsAtFuel roots` | 2026-07-31 | Bounded continuation Nash now receives its root scope explicitly |
| `IsBehavioralNashOnDesignatedContinuationsAtFuel` | `IsBehavioralNashOnRootsAtFuel roots` | 2026-07-31 | Bounded behavioral continuation Nash now receives its root scope explicitly |
| `IsMixedNashOnDesignatedContinuationsAtFuel` | `IsMixedNashOnRootsAtFuel roots` | 2026-07-31 | Bounded mixed continuation Nash now receives its root scope explicitly |
| `PureTerminating` | `PureTerminatingOnRoots roots` | 2026-07-31 | Termination is stated on an explicit family of continuation roots |
| `IsPureNashOnDesignatedContinuations` | `IsPureNashOnRoots roots` | 2026-07-31 | Unbounded continuation Nash now receives its root scope explicitly |
| `PureStrategy.toGeneral` | `PureStrategy.toDiscreteGeneral` | 2026-07-31 | Same pure-to-behavioral Dirac embedding |
| `PureProfile.toGeneral` | `PureProfile.toDiscreteGeneral` | 2026-07-31 | Same componentwise embedding |
| `GeneralProfile.behavioralProfileLaw` | `DiscreteGeneralProfile.behavioralProfileLaw` | 2026-07-31 | Same independent PMF product |
| `GeneralProfile.deviate` | `DiscreteGeneralProfile.deviate` | 2026-07-31 | Same component update |
| `GeneralProfile.deviate_same` | `DiscreteGeneralProfile.deviate_same` | 2026-07-31 | Same update-at-player theorem |
| `GeneralProfile.deviate_of_ne` | `DiscreteGeneralProfile.deviate_of_ne` | 2026-07-31 | Same update-away-from-player theorem |

This alias is eligible for `@[deprecated replacement]` because its theorem
statement is unchanged.  Endpoint versus occurrence strategies, state
re-rooting versus lawful subgames, and designated-root versus complete-system
solution concepts do not receive such aliases: their semantics differ.

## Completed root migration

On 2026-07-30 the root replaced `Interface.Execution.Discrete` with
`Interface.Execution.Finite`. Infinite path laws are available from
`Interface.Execution.Infinite` or the old supported compatibility aggregate.
The historical endpoint `GameTreeSPE`, `GameTreeNE`, and
`GameTreeStrategicForm` modules, the niche `FiniteArenaExtraction` bridge, and
`Zermelo` also became explicit imports.

Existing examples now import the implementation paths they use, and
`RootImportBoundary` checks both the retained finite surface and the removed
transitive names. The granular facade and examples builds are the migration
regressions. No theorem, declaration, namespace, or public module path was
deleted by this root-only dependency change.
