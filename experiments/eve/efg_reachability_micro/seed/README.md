# Public Stage 1a EFG reachability micro-pilot seed

This is a public synthetic/local usability task, not a benchmark or a model
capability evaluation. The only editable path is `Candidate.lean`. The
evaluator, accepted fixture, protected hashes, configuration, prompts, and
scoring logic are outside this solver workspace.

Use only the existing import already present in `Candidate.lean`:

```lean
import EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore
```

Preserve every declaration above the `Solver declarations` marker. Below that
marker, add these declarations in namespace
`EconCSLibEvEEFGReachabilityMicro`, with exactly the displayed types:

```lean
theorem reachability_history_bridge
    (A : Arena) (start finish : A.State) :
    A.Reachable start finish ↔ Nonempty (A.History start finish)

theorem left_reachable :
    diamondArena.Reachable DiamondState.root DiamondState.merged

theorem right_reachable :
    diamondArena.Reachable DiamondState.root DiamondState.merged

theorem reachability_proofs_eq :
    leftHistory.toReachable = rightHistory.toReachable

theorem histories_ne : leftHistory ≠ rightHistory

theorem occurrence_endpoints_eq : leftOccurrence.1 = rightOccurrence.1

theorem occurrences_ne : leftOccurrence ≠ rightOccurrence
```

The public core already contains the logical bridge. Use the smallest existing
interface rather than recreating a core theorem. `Reachable` is a proposition;
the concrete `History` and `HistoryFrom` values retain occurrences. Do not
claim an equivalence between reachability proof objects and histories, and do
not add a choice function merely to prove the required existential statement.

Do not use `sorry`, `admit`, `axiom`, `constant`, `unsafe`, `opaque`,
`native_decide`, `run_tac`, `#eval`, linter suppression, or another trusted
bypass. All warnings are failures.
