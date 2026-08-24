# EFG semantic execution regimes

This note is the authoritative ownership and bridge contract for the distinct
EFG execution regimes. Lean declarations remain authoritative for individual
definitions and theorems; [`efg-preservation-matrix.md`](efg-preservation-matrix.md)
remains authoritative for the strength of each proved relation.

The regimes are deliberately not fields of one universal game record. They
share structural occurrences and, where a full lawful probability is
available, a representation-independent path-law comparison layer. This
factorization avoids imposing countability on analytic models or measurability
on structural and finite models.

## Ownership ledger

| Regime | Native owner or producer | Recommended facade | Common-law status | What is not supplied |
|---|---|---|---|---|
| Structural occurrence semantics | `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled` | `EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore` | No probability law; owns the common history and legal-play predicates | chance normalization, execution, utility, and equilibrium |
| Finite discrete PMF execution | `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Discrete` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | Bounded history PMFs only; does not import the full measure-valued path-law carrier | infinite path measure and non-atomic kernels |
| Infinite discrete execution | `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.DiscretePath` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite` | Constructs `CompletePathLawSemantics` from the PMF behavioral executor | non-atomic action kernels and arbitrary-measure behavioral strategies |
| Analytic kernel execution | `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Analytic` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` | Constructs the same `CompletePathLawSemantics` from an explicitly lawful measurable-kernel presentation | automatic legality for an arbitrary stochastic-state kernel or a canonical measurable strategy space |
| Simultaneous FOSG frontend | `EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSG` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete` | Compiler-specific weak serialization, finite-horizon laws, and couplings only | strict EFG isomorphism, a general complete-path-law adapter, and standard SPE preservation |

`ControlledObservedGame.CompletePathLawSemantics`, owned by
`EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law`, is the maximum
common probability-law carrier. It stores normalized, almost-surely legal
per-root complete-path marginals. It intentionally stores no PMF, local
kernel, countability assumption, strategic-mode tag, payoff, or claim that
the marginals are one common causal process. Local execution coherence,
restart consistency, conditioning, and cross-root coherence remain separate
certificates.

## Direction of adapters

The dependency direction is fixed:

```text
structural occurrences
        |
        v
common lawful complete-path marginals
       / \
      /   \
PMF executor  measurable-kernel executor

FOSG --weak serialization/coupling--> discrete observed EFG
```

The common path-law module may not import either concrete producer. The
discrete and analytic adapters import the common carrier and prove that their
existing executor realizes it. The FOSG route remains a frontend/compiler:
it acquires a common path-law conclusion only when a named compiler-specific
realization or coupling theorem actually supplies one.

## Claim discipline

Every generality claim must use one of these labels:

- **native**: represented directly by the structural occurrence carrier;
- **adapter-backed**: a concrete executor constructs the common lawful
  path-law carrier;
- **compiler-backed**: a frontend theorem states the exact preserved axes;
- **open**: no Lean declaration currently closes the requested semantic axis.

“Supported by EconCSLib” is not by itself a preservation statement. In
particular, a PMF theorem does not cover non-atomic kernels, a weak serializer
does not provide a strict isomorphism, and equality of bounded marginals does
not provide equality of full path laws without a named bridge.

## Governed import consequences

`scripts/check_efg_governance.py` checks the following route boundaries:

1. finite execution contains no full path-law or analytic adapter;
2. infinite discrete execution contains the common law and discrete adapter,
   but no analytic adapter or measurable-kernel arena;
3. analytic execution contains the common law, both concrete adapters, and
   the measurable-kernel arena;
4. discrete compilation and the FOSG sequentializer contain no common
   full-path or analytic execution implementation;
5. the common law does not depend on either producer adapter.

The checker establishes import ownership, not mathematical preservation.
Cross-regime conclusions still require the declarations catalogued in the
preservation matrix.
