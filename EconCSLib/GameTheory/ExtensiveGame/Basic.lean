/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Basic
import Mathlib.Tactic.FinCases

/-!
# EconCSLib.GameTheory.ExtensiveGame.Basic

Extensive-form games built on a minimal **Arena** abstraction.

## Design

The design follows the Bourbaki principle — separate concerns into independent layers:

* **Arena** — pure dynamics: states, actions, transitions. No players, no payoffs.
  Terminal states are those where `Action s` is empty (no separate `isTerminal` Prop).
* **ControlledGame** — adds an initial state and player assignment to an Arena,
  but no outcome or payoff.
* **ExtensiveGame** — the compatibility layer that adds a state payoff to a
  ControlledGame.

This state-space approach supports both finite and infinite games.
Inductive game trees compile as a special case (see
`ExtensiveGame/Compiler/GameTreeObserved.lean` and its occurrence-sensitive
companion).

## Main definitions

* `Arena` — states + actions + transitions
* `Arena.IsTerminal` — a state with no available actions
* `ControlledGame` — arena + initial state + players
* `ExtensiveGame` — controlled game + state payoff
* Helper notation for building concrete games

## References

* [MSZ] Maschler, Solan, Zamir, *Game Theory*, Chapter 3
-/

/-! ### Arena -/

/-- A game arena: the pure dynamics of an extensive-form game.

    States, actions, and transitions. No players, no payoffs, no probability.
    A state is terminal iff `Action s` is empty. -/
structure Arena where
  /-- The state space. -/
  State : Type*
  /-- Available actions at each state. Empty = terminal. -/
  Action : State → Type*
  /-- Transition function: state + action → next state. -/
  next : (s : State) → Action s → State

namespace Arena

variable (A : Arena)

/-- A state is terminal if there are no available actions. -/
def IsTerminal (s : A.State) : Prop := IsEmpty (A.Action s)

/-- A state is a decision point if there is at least one action. -/
def IsDecision (s : A.State) : Prop := Nonempty (A.Action s)

/-- Terminal and decision are complementary. -/
theorem isTerminal_iff_not_isDecision (s : A.State) :
    A.IsTerminal s ↔ ¬ A.IsDecision s := by
  simp [IsTerminal, IsDecision, isEmpty_iff, not_nonempty_iff]

end Arena

/-! ### Payoff-free controlled games -/

/-- A payoff-free controlled extensive-game skeleton.

`ControlledGame` adds only a distinguished initial state and a mover label to
the pure `Arena` dynamics. It deliberately stores no objective, payoff,
probability law, finiteness, decidability, or information data. Logical games
can therefore use this carrier without inventing a utility type.

`mover s = none` denotes nature at a nonterminal state. As for
`ExtensiveGame`, the mover label at a terminal state is semantically ignored
unless a separate well-formedness certificate normalizes it. -/
structure ControlledGame (N : Type*) extends Arena where
  /-- The initial state (root of the controlled game). -/
  init : State
  /-- Who controls each state. `none` = chance or nature. -/
  mover : State → Option N

namespace ControlledGame

variable {N : Type*}

/-- Add an initial state and mover assignment to an ordinary arena. -/
abbrev ofArena (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N) :
    ControlledGame N where
  toArena := arena
  init := init
  mover := mover

@[simp]
theorem ofArena_toArena (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N) :
    (ofArena arena init mover).toArena = arena :=
  rfl

@[simp]
theorem ofArena_init (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N) :
    (ofArena arena init mover).init = init :=
  rfl

@[simp]
theorem ofArena_mover (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N) (state : arena.State) :
    (ofArena arena init mover).mover state = mover state :=
  rfl

/-- The arena of a payoff-free controlled game. -/
abbrev arena (G : ControlledGame N) : Arena := G.toArena

/-- Available actions at a state. -/
abbrev actions (G : ControlledGame N) (s : G.State) := G.Action s

/-- A state is terminal. -/
abbrev isTerminal (G : ControlledGame N) (s : G.State) :=
  G.toArena.IsTerminal s

/-- A state is controlled by player `i`. -/
def isPlayerState (G : ControlledGame N) (s : G.State) (i : N) : Prop :=
  G.mover s = some i

/-- A nonterminal state controlled by nature. -/
def isChanceState (G : ControlledGame N) (s : G.State) : Prop :=
  G.mover s = none ∧ ¬ G.toArena.IsTerminal s

/-- No chance nodes: every nonterminal state has a strategic mover. -/
def NoChance (G : ControlledGame N) : Prop :=
  ∀ s : G.State, ¬ G.isTerminal s → ∃ i : N, G.mover s = some i

end ControlledGame

/-! ### Extensive-form game -/

/-- A state-payoff extensive game: a payoff-free controlled game together
with a convenient endpoint-state payoff.

    * `mover s` = who controls state `s` (`none` = chance or nature)
    * `payoff s i` = payoff for player `i` at state `s` (meaningful at terminal states)

    General terminal-history, complete-path, and winning-condition semantics
    are separate objective layers; this field is not their authoritative
    definition.

    No `isTerminal` field — terminal states are detected by `IsEmpty (Action s)`.
    No proof terms to carry around. -/
