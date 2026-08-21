import EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore

/-!
# EvE Stage 1a EFG reachability/history micro-pilot

This public local task uses only the StructuralCore facade. Preserve the fixed
diamond data above the solver marker, then add the declarations named in the
seed README. Do not add another import or modify any other file.
-/

namespace EconCSLibEvEEFGReachabilityMicro

/-- States of the fixed merged-endpoint regression. -/
inductive DiamondState
  | root
  | merged

/-- Two distinct actions from the root merge at one terminal endpoint. -/
def diamondArena : Arena where
  State := DiamondState
  Action
    | .root => Bool
    | .merged => PEmpty
  next
    | .root, _ => .merged

/-- The false-action history. -/
def leftHistory :
    diamondArena.History DiamondState.root DiamondState.merged :=
  Arena.History.nil.snoc false

/-- The true-action history. -/
def rightHistory :
    diamondArena.History DiamondState.root DiamondState.merged :=
  Arena.History.nil.snoc true

/-- The left occurrence in the history unfolding. -/
def leftOccurrence : diamondArena.HistoryFrom DiamondState.root :=
  ⟨DiamondState.merged, leftHistory⟩

/-- The right occurrence in the history unfolding. -/
def rightOccurrence : diamondArena.HistoryFrom DiamondState.root :=
  ⟨DiamondState.merged, rightHistory⟩

/-! ## Solver declarations -/

theorem reachability_history_bridge
    (A : Arena) (start finish : A.State) :
    A.Reachable start finish ↔ Nonempty (A.History start finish) := by
  exact A.reachable_iff_nonempty_history start finish

theorem left_reachable :
    diamondArena.Reachable DiamondState.root DiamondState.merged := by
  exact leftHistory.toReachable

theorem right_reachable :
    diamondArena.Reachable DiamondState.root DiamondState.merged := by
  exact rightHistory.toReachable

theorem histories_ne : leftHistory ≠ rightHistory := by
  intro h
  cases h

theorem occurrence_endpoints_eq : leftOccurrence.1 = rightOccurrence.1 := by
  exact

end EconCSLibEvEEFGReachabilityMicro
