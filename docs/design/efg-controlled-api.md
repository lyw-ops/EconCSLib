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
    │   └── Recall.lean
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
| Evaluator-relative continuation equilibrium | `Observed.Controlled.Semantics` |
| Finite discrete chance/history laws | `Observed.Controlled.Law.Discrete` |
| Representation-independent complete-path laws | `Observed.Controlled.Law` |
| Discrete complete-path realization | `Observed.Controlled.Law.DiscretePath` |
| Analytic-kernel complete-path realization | `Observed.Controlled.Law.Analytic` |
| One infrastructure responsibility | `Observed.Controlled.Infrastructure.<leaf>` |
| One morphism responsibility | `Observed.Controlled.Morphism.<leaf>` |
| Broad payoff-free infrastructure | `Observed.Controlled.Infrastructure` |
| Broad payoff-free morphism transport | `Observed.Controlled.Morphism` |
| Payoff-aware bridge only | `Observed.Controlled.Compat.<adapter>` |

## Semantic contract boundaries

- `ControlledGame.NoChance` quantifies over the whole ambient state carrier.
  `ControlledGame.NoChanceOnHistories` quantifies only over legal complete
  histories from `init`, and is the certificate used by canonical pure
  execution, total continuation, winning, and determinacy APIs. Global
  no-chance implies the reachable form.
- `PureStrategyAvailabilityCertificate` packages only represented decision
  information and mover coherence.
  `ReachablePureStrategyModelCertificate` adds reachable no-chance. Neither
  bundle contains finiteness, payoff, probability, recall, or termination.
- `ContinuationSemantics` alone is an arbitrary evaluator. Its generic
  solution concept is named evaluator-relative. There is intentionally no
  generic standard-SPE name until concrete execution layers expose a common
  canonical root-local strategy, deviation, and complete-path interface.
- `BoundedHistoryLawFamily` is raw per-profile PMF data.
  `CertifiedBehavioralExecutionLaw` adds normalization, reachable legality,
  terminal absorption, and equality with the concrete behavioral executor.
- `CompletePathLawSemantics` is a family of lawful per-root path marginals. It
  does not by itself construct one common causal process; restart,
  conditioning, and execution coherence require separate certificates.
- Signal/public recall is explicitly event-clock recall: every arena
  transition contributes one signal. `SignalTraceBuilder` is the optional
  external layer for asynchronous models and permits `none` as a silent
  event. The always-emitting builder recovers the event-clock trace; no
  equivalence with arbitrary silent-event builders is claimed.

Application code should normally import a stable `Interface.*` facade rather
than an implementation module above.

## Enforced hierarchy invariants

`scripts/check_efg_governance.py` verifies all of the following:

1. the complete `Observed.Controlled` hierarchy is exactly the registered
   carrier, five semantic owners, nine responsibility owners, two aggregate
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
compatibility policy must be introduced deliberately after a stable public API
is declared.
