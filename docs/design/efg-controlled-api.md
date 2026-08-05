# Controlled EFG module map

The payoff-free observed EFG stack is physically grouped under
`Observed/Controlled/`. `Observed/Controlled.lean` remains the minimal carrier;
all semantic, infrastructure, morphism, law, and payoff-aware adapter modules
live below that carrier path.

This is a hard pre-stability module-path migration. The former flat
`Observed/ControlledFoo.lean` paths are intentionally absent rather than kept
as forwarding stubs.

## Canonical hierarchy

```text
Observed/
├── Controlled.lean
└── Controlled/
    ├── Semantics.lean
    ├── Infrastructure.lean
    ├── Infrastructure/
    │   ├── Core.lean
    │   ├── WellFormed.lean
    │   ├── Subgame.lean
    │   ├── Finite.lean
    │   ├── Quasi.lean
    │   └── Recall.lean
    ├── Morphism.lean
    ├── Morphism/
    │   ├── Core.lean
    │   ├── Subgame.lean
    │   ├── Recall.lean
    │   └── Objective.lean
    ├── Law.lean
    ├── Law/
    │   ├── Discrete.lean
    │   ├── DiscretePath.lean
    │   └── Analytic.lean
    └── Compat/
        ├── Infrastructure.lean
        ├── Morphism.lean
        └── DiscreteLaw.lean
```

`Controlled.Infrastructure` and `Controlled.Morphism` are canonical,
declaration-free aggregate facades. They are convenient broad entry points;
implementation code should still import the narrowest responsibility leaf.
The `Controlled.Compat.*` directory is not a registry of legacy import-only
wrappers: those files contain downstream payoff-aware adapter declarations
and are classified Internal.

## Module roles

| Role | Modules | May own declarations? |
|---|---|---:|
| Minimal carrier | `Controlled` | Yes |
| Semantic owners | `Controlled.Semantics`, `Controlled.Law`, `Controlled.Law.{Discrete,DiscretePath,Analytic}` | Yes |
| Responsibility owners | `Controlled.Infrastructure.*`, `Controlled.Morphism.*` leaves | Yes |
| Aggregate facades | `Controlled.Infrastructure`, `Controlled.Morphism` | No |
| Payoff-aware adapters | `Controlled.Compat.{Infrastructure,Morphism,DiscreteLaw}` | Only downstream bridge declarations |

Payoff-free declarations remain under `ControlledObservedGame` or
`DiscreteControlledObservedChanceGame`. Adapter declarations are isolated
under `ObservedGame` or `ObservedChanceGame`; moving their files does not
change those mathematical namespaces.

## Import selection

| Need | Import |
|---|---|
| Base payoff-free observation/information record | `Observed.Controlled` |
| Pure terminal/path-objective continuation and evaluator-relative semantics | `Observed.Controlled.Semantics` |
| Finite discrete chance/history laws | `Observed.Controlled.Law.Discrete` |
| Representation-independent complete-path laws | `Observed.Controlled.Law` |
| Discrete complete-path realization | `Observed.Controlled.Law.DiscretePath` |
| Analytic-kernel complete-path realization | `Observed.Controlled.Law.Analytic` |
| One infrastructure responsibility | `Observed.Controlled.Infrastructure.<leaf>` |
| One morphism responsibility | `Observed.Controlled.Morphism.<leaf>` |
| Broad payoff-free infrastructure | `Observed.Controlled.Infrastructure` |
| Broad payoff-free morphism transport | `Observed.Controlled.Morphism` |
| Payoff-aware bridge only | `Observed.Controlled.Compat.<adapter>` |

`Controlled.Morphism.Objective` is the operational boundary for strict
terminal-objective preservation. It requires an explicit
`TerminalObjectiveCompatible` commuting square; a structural isomorphism does
not automatically preserve a caller-supplied history objective.

## Semantic contract boundaries

- `ControlledObservedGame.infoAt`, `infoAt_observe`, and `actionEquiv` are
  defined only at a nonterminal history whose mover is the named player.
  Consequently a terminal endpoint carrying an unnormalized `some i` label
  never creates a decision-information value or pure-strategy coordinate.
  `DecisionMoverCoherent` remains the optional stronger certificate for
  presentations that normalize reachable terminal mover labels to `none`.
- `ControlledGame.NoChance` quantifies over the whole ambient state carrier.
  `ControlledGame.NoChanceOnHistories` quantifies only over legal complete
  histories from `init`, and is the certificate used by canonical pure
  execution, total continuation, winning, and determinacy APIs. Global
  no-chance implies the reachable form.
- `PureStrategyAvailabilityCertificate` packages only represented decision
  information and mover coherence.
  `ReachablePureStrategyModelCertificate` adds reachable no-chance. Neither
  bundle contains finiteness, payoff, probability, recall, or termination.
- `terminalObjectiveContinuationGameForm` and
  `pathObjectiveContinuationGameForm` execute the canonical full pure
  strategy space and therefore support operationally named Nash/SPE
  predicates. `ContinuationSemantics` alone remains an arbitrary evaluator;
  its generic solution concepts stay explicitly evaluator-relative.
- `BoundedHistoryLawFamily` is raw per-profile PMF data.
  `CertifiedBehavioralExecutionLaw` adds normalization, reachable legality,
  terminal absorption, and equality with the concrete behavioral executor.
  Its derived `exists_suffix_of_mem_support` theorem proves every support
  endpoint is the supplied current history followed by a legal typed suffix;
  this is stronger and more reusable than root reachability alone.
- `CompletePathLawSemantics` is a family of lawful per-root path marginals. It
  does not by itself construct one common causal process; restart,
  conditioning, and execution coherence require separate certificates.
- Signal/public recall is explicitly event-clock recall: every arena
  transition contributes one signal. `SignalTraceBuilder` is the optional
  external layer for asynchronous models and permits `none` as a silent
  event. The always-emitting builder recovers the event-clock trace; no
  equivalence with arbitrary silent-event builders is claimed.

Application code should normally import a canonical pre-stability
`Interface.*` facade rather than an implementation module above. These
facades are governed recommendations, not current external
source-compatibility guarantees.

## Payoff-aware convergence audit

The post-freeze ownership audit classifies the remaining parallel-looking
surface as follows:

| Surface | Classification | Authoritative owner |
|---|---|---|
| observation, public observation, decision information, and information actions | necessary state-payoff carrier projection | `ControlledObservedGame`; `ObservedGame.toControlledObservedGame` forgets only payoff |
| pure strategy and pure profile carriers | definitional payoff-aware spelling | `ControlledObservedGame.PureStrategy` / `PureProfile` |
| decision-information witness | definitional payoff-aware spelling | `ControlledObservedGame.DecisionInfoWitness` |
| represented-information and mover-coherence predicates | definitional payoff-aware spelling | `ControlledObservedGame.AllDecisionInfoRepresented` / `DecisionMoverCoherent` |
| finite-EFG certificate | definitional payoff-aware spelling | `ControlledObservedGame.FiniteEFGHypotheses` |
| discrete behavioral strategy/profile carriers | definitional payoff-aware spelling | `ControlledObservedGame.BehavioralStrategy` / `BehavioralProfile` in `Controlled.Law.Discrete` |
| no-chance pure history execution | canonical semantics plus payoff-aware continuation wrapper | controlled infrastructure owns the history policy; `ObservedGame` adds stopped payoff interpretation |
| discrete chance kernel | necessary probability adapter | `DiscreteControlledObservedChanceGame`; payoff attachment/forgetting has two round trips |
| terminal state payoff and payoff-compatible morphism square | genuinely payoff-aware semantics | `ObservedGame` and `ObservedGame.PayoffCompatibleIso` |

`ObservedGame` remains a necessary downstream carrier because an endpoint
state payoff is real additional data. It is not a second owner of pure,
behavioral, represented-information, or finite certificates. The
`ofControlledObservedGame`/`toControlledObservedGame` and
`ofDiscreteControlledObservedChanceGame`/
`toDiscreteControlledObservedChanceGame` round trips make the additive data
boundary explicit.

## Enforced hierarchy invariants

`scripts/check_efg_governance.py` verifies all of the following:

1. the complete `Observed.Controlled` hierarchy is exactly the registered
   carrier, five semantic owners, ten responsibility owners, two aggregate
   facades, and three payoff-aware adapters;
2. a new flat sibling such as `Observed.ControlledFoo` is rejected;
3. every module role has the matching lifecycle status;
4. each adapter has an exact direct-import contract and declares only under
   its payoff-aware namespace;
5. no canonical controlled module reaches a payoff-aware adapter, even
   transitively;
6. the infrastructure and morphism leaves retain their exact governed
   closures; and
7. `ControlledApiImportBoundary` jointly imports every public role
   and checks that canonical and payoff-aware declarations coexist.

The same checker inventories all source modules with no declarations. The two
controlled aggregates must contain only their exact imports and a module
docstring identifying the canonical aggregate role; unregistered import-only,
zero-byte, and comment/namespace-only Lean files are rejected.

No compatibility stub is kept at a former flat path. Any future module-path
compatibility policy must be introduced deliberately if a stable public EFG
API is declared in the future.
