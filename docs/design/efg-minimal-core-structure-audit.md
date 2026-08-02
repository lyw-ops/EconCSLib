# EFG Minimal-Core Structure Audit

**Snapshot:** 2026-08-02 · **Scope:** payoff-free foundations and their
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
accuracy, not the mathematical carrier.

| Property | Verdict | Source-based reason |
|---|---|---|
| Data-record minimality | Pass | The three records and their fields are unchanged. |
| Literal structural import boundary | Pass, F1 resolved | `Interface.StructuralCore` has the exact five-module EFG/local closure enforced by governance. |
| Infrastructure cohesion | Pass, F2 resolved | Six responsibility leaves now separate execution, general well-formedness, subgames, finite certificates, quasistrategies, and recall; the old path is import-only. |
| Morphism layering | Pass, F7 resolved | Structural, lawful-subgame, and recall transport have separate exact closures; the old `ControlledMorphism` path is import-only. |
| Foundation-facade accuracy | Pass | `Interface.Core` is documented and governed as a Foundation Facade, not as the literal core. |
| Objective/payoff neutrality | Pass through generic continuation/SPE semantics | Core reaches neither `Execution.Objective` nor `Winning.*` nor payoff-aware `Observed.Game`; `ContinuationSemantics` and its generic standard-SPE theorem are owned by `ControlledObservedGame`. |
| Probability neutrality | Pass at StructuralCore; bounded PMF is intentional in Core | StructuralCore has no PMF module; Core intentionally imports `StochasticExecution`. |
| Assumption generality | Pass | Finiteness, decidability, recall, termination, and measurability remain external. |
| Player-label compatibility | Pass for bijections | `relabelPlayers` reindexes mover, observation, information, actions, presentations, profiles, and lawful/complete subgame systems without changing Arena histories. |
| Representation compatibility | Pass with explicit preservation claims | Compilers and relations retain their existing preservation packages; absence from a package is not inferred. |
| Current validation health | Source and mathematical gates pass; branch is not merge-ready | Clean aggregate/example builds and semantic/governance checks pass, but the two existing branch commits violate the repository's one-file-per-commit CI rule. |

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
