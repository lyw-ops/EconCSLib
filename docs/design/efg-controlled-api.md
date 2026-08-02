# Controlled EFG module map

The `Observed/Controlled*.lean` filenames do not represent competing versions
of one API. They form four deliberately disjoint roles. The governance checker
fixes the complete flat set and rejects unclassified additions, so another
`Controlled*.lean` file cannot silently appear without an architectural
decision.

## Flat-module roles

| Role | Modules | May own declarations? | Import direction |
|---|---|---:|---|
| Canonical carrier | `Controlled` | Yes | Lowest payoff-free observed layer |
| Canonical semantic owners | `ControlledSemantics`, `ControlledDiscreteLaw`, `ControlledLaw`, `ControlledDiscretePathLaw`, `ControlledAnalyticLaw` | Yes | Depend on the carrier or narrower canonical prerequisites |
| Legacy import aggregates | `ControlledInfrastructure`, `ControlledMorphism` | No | Re-export their responsibility leaves for old import paths |
| Payoff-aware adapters | `ControlledInfrastructureCompat`, `ControlledMorphismCompat`, `ControlledDiscreteLawCompat` | Yes, only downstream adapter declarations | Project from `ObservedGame`/`ObservedChanceGame` to canonical controlled owners |

The two legacy aggregates and the three `*Compat` adapters are not synonyms:

- an **aggregate** preserves an old broad import path and contains no
  declaration;
- a **payoff-aware adapter** contains explicit bridge declarations in
  `ObservedGame` or `ObservedChanceGame`;
- neither is a canonical payoff-free owner.

## Responsibility directories

The broad implementation families are already physically grouped:

```text
ControlledInfrastructure/
  Core  WellFormed  Subgame  Finite  Quasi  Recall

ControlledMorphism/
  Core  Subgame  Recall
```

New implementation code imports the narrowest leaf. The corresponding flat
aggregate exists only for source compatibility and is rejected as an
implementation dependency.

## Import selection

| Need | Import |
|---|---|
| Base payoff-free observation/information record | `Observed.Controlled` |
| Generic continuation and standard-SPE semantics | `Observed.ControlledSemantics` |
| Finite discrete chance/history laws | `Observed.ControlledDiscreteLaw` |
| Representation-independent complete-path laws | `Observed.ControlledLaw` |
| Discrete complete-path realization | `Observed.ControlledDiscretePathLaw` |
| Analytic-kernel complete-path realization | `Observed.ControlledAnalyticLaw` |
| One infrastructure responsibility | `Observed.ControlledInfrastructure.<leaf>` |
| One morphism responsibility | `Observed.ControlledMorphism.<leaf>` |
| Existing client relying on the former broad imports | `Observed.ControlledInfrastructure` or `Observed.ControlledMorphism` |
| Payoff-aware bridge only | the corresponding `*Compat` module |

Application code should normally import a stable `Interface.*` facade rather
than any implementation module above.

## Enforced non-conflict invariants

`scripts/check_efg_governance.py` verifies all of the following:

1. the flat family is exactly one carrier, five canonical semantic owners, two
   declaration-free aggregates, and three payoff-aware adapters;
2. every flat role has the matching lifecycle status;
3. each adapter has an exact direct-import contract and declares only under
   its payoff-aware namespace;
4. no canonical controlled owner reaches a payoff-aware adapter, even
   transitively;
5. implementation modules cannot import the two compatibility aggregates;
6. the infrastructure and morphism leaves retain their exact governed
   closures; and
7. `ControlledCompatibilityImportBoundary` jointly imports the complete flat
   family and checks that canonical and payoff-aware names coexist in their
   intended namespaces.

Physically renaming the established flat paths would require keeping new stub
files at every old path, increasing rather than reducing the visible module
count. The role map plus one-way governance preserves compatibility without
creating a second set of canonical owners.
