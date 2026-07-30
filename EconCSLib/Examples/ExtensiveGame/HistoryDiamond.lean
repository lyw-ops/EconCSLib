/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.History

/-!
# EconCSLib.Examples.ExtensiveGame.HistoryDiamond

A regression example showing that history unfolding preserves distinct paths
that merge at the same Arena state.
-/

namespace Examples.HistoryDiamond

/-- A root with two distinct actions that lead to the same terminal state. -/
inductive State
  | root
  | terminal

/-- The diamond Arena has two histories to one endpoint. -/
def arena : Arena where
  State := State
  Action
    | .root => Bool
    | .terminal => PEmpty
  next
    | .root, _ => .terminal

/-- The history taking the first root action. -/
def left : arena.History State.root State.terminal :=
  Arena.History.nil.snoc false

/-- The history taking the second root action. -/
def right : arena.History State.root State.terminal :=
  Arena.History.nil.snoc true

/-- Distinct actions remain distinct histories even though their endpoint is
the same world state. -/
theorem left_ne_right : left ≠ right := by
  intro h
  cases h

end Examples.HistoryDiamond
