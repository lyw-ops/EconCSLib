/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.HistoryDiamond
import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete

/-!
# History-sensitive objective continuation regression

Two distinct one-step histories merge into the same terminal world state.
The payoff-free terminal-objective continuation semantics nevertheless
distinguishes them because it evaluates the complete accumulated history,
not only the endpoint.
-/

namespace Examples.HistoryObjectiveContinuation

open HistoryDiamond

/-- The diamond dynamics controlled by one player at its root. -/
def base : ControlledGame Unit where
  toArena := arena
  init := State.root
  mover
    | .root => some ()
    | .terminal => none

/-- Complete information is sufficient for the one-decision regression. -/
abbrev game : ExtensiveGame.ControlledObservedGame Unit :=
  ExtensiveGame.ControlledObservedGame.completeInformation base

noncomputable local instance terminalDecidable :
    (state : base.State) → Decidable (base.isTerminal state) :=
  fun _state => Classical.propDecidable _

/-- The controlled diamond has no non-player-controlled reachable decision. -/
theorem noChance : base.NoChance := by
  intro state hnonterminal
  cases state with
  | root =>
      exact ⟨(), rfl⟩
  | terminal =>
      exact False.elim
        (hnonterminal (by
          show IsEmpty PEmpty
          infer_instance))

/-- Reachable no-chance certificate used by pure continuation execution. -/
def noChanceOnHistories : base.NoChanceOnHistories :=
  noChance.noChanceOnHistories

/-- The left and right absolute histories, sharing one terminal endpoint. -/
def leftCurrent : base.History :=
  ⟨State.terminal, left⟩

def rightCurrent : base.History :=
  ⟨State.terminal, right⟩

theorem leftCurrent_terminal :
    base.isTerminal leftCurrent.1 := by
  show IsEmpty PEmpty
  infer_instance

theorem rightCurrent_terminal :
    base.isTerminal rightCurrent.1 := by
  show IsEmpty PEmpty
  infer_instance

theorem rightCurrent_ne_leftCurrent :
    rightCurrent ≠ leftCurrent := by
  intro heq
  have hhistory : right = left := by
    cases heq
  exact left_ne_right hhistory.symm

/-- Every profile is already terminal at the left continuation. -/
theorem pureTerminatingAt_left :
    game.PureTerminatingAt noChanceOnHistories leftCurrent :=
  fun _profile =>
    ⟨0, leftCurrent_terminal⟩

/-- Every profile is already terminal at the right continuation. -/
theorem pureTerminatingAt_right :
    game.PureTerminatingAt noChanceOnHistories rightCurrent :=
  fun _profile =>
    ⟨0, rightCurrent_terminal⟩

/-- Route-sensitive objective: the left occurrence is false and every other
terminal occurrence is true. -/
noncomputable def routeObjective :
    base.toArena.TerminalOutcome base.init Bool := by
  classical
  exact fun terminalHistory =>
    if terminalHistory.1 = leftCurrent then false else true

/-- One arbitrary complete pure profile; only its type is relevant at the two
already-terminal continuations. -/
noncomputable def profile : game.PureProfile :=
  fun _player information =>
    Classical.choice (not_isEmpty_iff.mp information.2.2)

/-- The left continuation evaluates the left occurrence. -/
theorem left_outcome :
    (game.terminalObjectiveContinuationGameForm
      routeObjective noChanceOnHistories leftCurrent
      pureTerminatingAt_left).outcome profile = false := by
  classical
  change
    (if game.terminalHistoryFrom profile noChanceOnHistories
          leftCurrent (pureTerminatingAt_left profile) = leftCurrent
      then false else true) = false
  rw [game.terminalHistoryFrom_eq_of_terminal
    profile noChanceOnHistories leftCurrent
    (pureTerminatingAt_left profile) 0 leftCurrent_terminal]
  simp

/-- The right continuation evaluates the distinct right occurrence despite
sharing the left continuation's endpoint state. -/
theorem right_outcome :
    (game.terminalObjectiveContinuationGameForm
      routeObjective noChanceOnHistories rightCurrent
      pureTerminatingAt_right).outcome profile = true := by
  classical
  change
    (if game.terminalHistoryFrom profile noChanceOnHistories
          rightCurrent (pureTerminatingAt_right profile) = leftCurrent
      then false else true) = true
  rw [game.terminalHistoryFrom_eq_of_terminal
    profile noChanceOnHistories rightCurrent
    (pureTerminatingAt_right profile) 0 rightCurrent_terminal]
  simp [rightCurrent_ne_leftCurrent]

/-- The two continuation game forms distinguish occurrence histories that an
endpoint-payoff semantics alone cannot distinguish. -/
theorem continuation_outcomes_ne :
    (game.terminalObjectiveContinuationGameForm
      routeObjective noChanceOnHistories leftCurrent
      pureTerminatingAt_left).outcome profile ≠
    (game.terminalObjectiveContinuationGameForm
      routeObjective noChanceOnHistories rightCurrent
      pureTerminatingAt_right).outcome profile := by
  rw [left_outcome, right_outcome]
  simp

/-- An endpoint-payoff observed game on the same controlled carrier. -/
def endpointGame : ExtensiveGame.ObservedGame Unit Bool :=
  ExtensiveGame.ObservedGame.ofControlledObservedGame game
    (fun state _player =>
      match state with
      | .root => false
      | .terminal => true)

noncomputable local instance endpointTerminalDecidable :
    (state : endpointGame.base.State) →
      Decidable (endpointGame.base.isTerminal state) :=
  fun _state => Classical.propDecidable _

/-- Adding endpoint payoffs does not change the controlled termination
certificate. -/
theorem endpointPureTerminatingAt_left :
    endpointGame.PureTerminatingAt noChanceOnHistories leftCurrent :=
  pureTerminatingAt_left

/-- The historical endpoint-payoff continuation is definitionally the
terminal-objective specialization on this concrete game. -/
theorem endpoint_payoff_specialization :
    endpointGame.terminalContinuationGameForm
        noChanceOnHistories leftCurrent
        endpointPureTerminatingAt_left =
      endpointGame.toControlledObservedGame.terminalObjectiveContinuationGameForm
          endpointGame.base.terminalPayoffOutcome
          noChanceOnHistories leftCurrent
          endpointPureTerminatingAt_left :=
  endpointGame.terminalContinuationGameForm_eq_terminalObjective
    noChanceOnHistories leftCurrent endpointPureTerminatingAt_left

end Examples.HistoryObjectiveContinuation
