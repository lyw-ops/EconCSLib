/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Defs
import Mathlib.Logic.IsEmpty.Basic

/-!
# Payoff-free structural carriers for extensive games

This module contains only the representation-neutral dynamics used by the
minimal EFG core.

## Main definitions

* `Arena` — states, dependent legal actions, and transitions.
* `Arena.IsTerminal` — terminality as absence of legal actions.
* `ControlledGame` — an Arena with a root and player-control labels.
* `Arena.ofFin` — a small constructor for explicitly finite arenas.

No payoff, objective, probability law, finiteness assumption, decidability
assumption, or information structure is stored in these carriers. In
particular, `mover s = none` is only a non-player-control label. A chance law,
when desired, belongs to a separate stochastic semantics layer.

This state-space representation permits merging paths, cycles, and infinite
state or action types. History unfolding is provided separately.
-/

/-- A game arena: the pure dynamics of an extensive-form game.

States, actions, and transitions are stored without players, payoffs, or
probability. A state is terminal iff `Action s` is empty. -/
structure Arena where
  /-- The state space. -/
  State : Type*
  /-- Available actions at each state. Empty means terminal. -/
  Action : State → Type*
  /-- Transition function from a state and one legal action. -/
  next : (s : State) → Action s → State

namespace Arena

variable (A : Arena)

/-- A state is terminal if there are no available actions. -/
def IsTerminal (s : A.State) : Prop := IsEmpty (A.Action s)

/-- A state is a decision point if it has at least one available action. -/
def IsDecision (s : A.State) : Prop := Nonempty (A.Action s)

/-- Terminal and decision states are complementary. -/
theorem isTerminal_iff_not_isDecision (s : A.State) :
    A.IsTerminal s ↔ ¬ A.IsDecision s := by
  simp [IsTerminal, IsDecision, isEmpty_iff, not_nonempty_iff]

end Arena
