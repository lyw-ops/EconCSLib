/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.History

/-!
# EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution

Terminal-aware, fuel-bounded execution for Arena histories.

The older `Arena.play` API takes a total chooser `(s : State) → Action s`.
Such a chooser cannot exist when terminal states have empty action types.  This
module instead uses a `HistoryPolicy`: an action is requested only together
with a proof that the current endpoint is nonterminal.  Execution stops
immediately at a terminal endpoint and otherwise appends exactly one typed
action to the accumulated history.

## Main definitions

* `Arena.HistoryPolicy` — a history-dependent action policy defined only at
  nonterminal endpoints.
* `Arena.stoppedHistoryFrom` — continue an accumulated history for at most the
  supplied fuel.
* `Arena.stoppedHistory` — execute from the empty history.
* `ExtensiveGame.stoppedPayoff` — a terminal payoff vector, returned only when
  execution actually reaches a terminal state.

## Main results

* `stopped_history_from_eq_self_of_terminal` — terminal histories are fixed points.
* `stopped_history_from_add` — execution composes by addition of fuel.
* `stopped_history_from_length_le` — a run appends at most `fuel` actions.
* `stopped_history_from_terminal_or_length_eq` — a run either terminates or uses
  every available step.
* `stopped_history_from_add_of_terminal` — once stopped, additional fuel has no
  effect.
* `stopped_history_from_eq_of_terminal` — any two terminating fuel bounds agree.
-/

namespace Arena

/-- A history-dependent policy that is queried only at nonterminal endpoints. -/
def HistoryPolicy (A : Arena) (start : A.State) : Type _ :=
  (h : A.HistoryFrom start) → ¬ A.IsTerminal h.1 → A.Action h.1

variable {A : Arena} {start : A.State}

/-- Continue an already accumulated history for at most `fuel` transitions.

At a terminal endpoint the history is returned unchanged.  At a nonterminal
endpoint the policy supplies one action, that action is appended, and execution
continues with one less unit of fuel. -/
def stoppedHistoryFrom
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start)
    (current : A.HistoryFrom start) : ℕ → A.HistoryFrom start
  | 0 => current
  | fuel + 1 =>
      if hterminal : A.IsTerminal current.1 then
        current
      else
        let action := policy current hterminal
        stoppedHistoryFrom policy
          ⟨A.next current.1 action, current.2.snoc action⟩ fuel

/-- Execute a history policy from the empty history for at most `fuel` steps. -/
def stoppedHistory
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (fuel : ℕ) :
    A.HistoryFrom start :=
  stoppedHistoryFrom policy (HistoryFrom.nil A start) fuel

@[simp]
theorem stopped_history_from_zero
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start) :
    stoppedHistoryFrom policy current 0 = current := rfl

@[simp]
theorem stopped_history_from_succ_of_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start)
    (fuel : ℕ) (hterminal : A.IsTerminal current.1) :
    stoppedHistoryFrom policy current (fuel + 1) = current := by
  simp [stoppedHistoryFrom, hterminal]

theorem stopped_history_from_succ_of_not_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start)
    (fuel : ℕ) (hterminal : ¬ A.IsTerminal current.1) :
    stoppedHistoryFrom policy current (fuel + 1) =
      stoppedHistoryFrom policy
        ⟨A.next current.1 (policy current hterminal),
          current.2.snoc (policy current hterminal)⟩ fuel := by
  simp [stoppedHistoryFrom, hterminal]

/-- A terminal accumulated history is a fixed point for every fuel value. -/
theorem stopped_history_from_eq_self_of_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start)
    (hterminal : A.IsTerminal current.1) :
    ∀ fuel, stoppedHistoryFrom policy current fuel = current
  | 0 => rfl
  | fuel + 1 => stopped_history_from_succ_of_terminal policy current fuel hterminal

/-- Running for `first + second` steps is the same as running for `first`
steps and then continuing the resulting history for `second` more steps. -/
theorem stopped_history_from_add
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start)
    (first second : ℕ) :
    stoppedHistoryFrom policy current (first + second) =
      stoppedHistoryFrom policy
        (stoppedHistoryFrom policy current first) second := by
  induction first generalizing current with
  | zero =>
      simp
  | succ first ih =>
      by_cases hterminal : A.IsTerminal current.1
      · rw [Nat.succ_add]
        rw [stopped_history_from_succ_of_terminal policy current _ hterminal]
        rw [stopped_history_from_succ_of_terminal policy current first hterminal]
        exact
          (stopped_history_from_eq_self_of_terminal
            policy current hterminal second).symm
      · rw [Nat.succ_add]
        rw [stopped_history_from_succ_of_not_terminal policy current _ hterminal]
        rw [stopped_history_from_succ_of_not_terminal policy current first hterminal]
        exact ih
          ⟨A.next current.1 (policy current hterminal),
            current.2.snoc (policy current hterminal)⟩

/-- Execution never appends more actions than the supplied fuel. -/
theorem stopped_history_from_length_le
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start) :
    ∀ fuel,
      (stoppedHistoryFrom policy current fuel).2.length ≤
        current.2.length + fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      simp
  | succ fuel ih =>
      by_cases hterminal : A.IsTerminal current.1
      · rw [stopped_history_from_succ_of_terminal policy current fuel hterminal]
        omega
      · rw [stopped_history_from_succ_of_not_terminal policy current fuel hterminal]
        have hle := ih
          ⟨A.next current.1 (policy current hterminal),
            current.2.snoc (policy current hterminal)⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle

/-- A fuel-bounded run either reaches a terminal endpoint or appends exactly
one action for every available unit of fuel. -/
theorem stopped_history_from_terminal_or_length_eq
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start) :
    ∀ fuel,
      A.IsTerminal (stoppedHistoryFrom policy current fuel).1 ∨
        (stoppedHistoryFrom policy current fuel).2.length =
          current.2.length + fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      by_cases hterminal : A.IsTerminal current.1
      · exact Or.inl hterminal
      · exact Or.inr (by simp)
  | succ fuel ih =>
      by_cases hterminal : A.IsTerminal current.1
      · rw [stopped_history_from_succ_of_terminal policy current fuel hterminal]
        exact Or.inl hterminal
      · rw [stopped_history_from_succ_of_not_terminal policy current fuel hterminal]
        rcases ih
            ⟨A.next current.1 (policy current hterminal),
              current.2.snoc (policy current hterminal)⟩ with hstopped | hlength
        · exact Or.inl hstopped
        · exact Or.inr (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength)

/-- Once a run has reached a terminal endpoint, adding more fuel cannot change
its result. -/
theorem stopped_history_from_add_of_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start)
    (first second : ℕ)
    (hterminal :
      A.IsTerminal (stoppedHistoryFrom policy current first).1) :
    stoppedHistoryFrom policy current (first + second) =
      stoppedHistoryFrom policy current first := by
  rw [stopped_history_from_add]
  exact stopped_history_from_eq_self_of_terminal policy _ hterminal second

/-- Any two fuel bounds that both reach a terminal endpoint produce exactly
the same accumulated history.

This is the uniqueness fact needed to turn existential termination into a
well-defined total terminal-outcome semantics. -/
theorem stopped_history_from_eq_of_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start)
    (first second : ℕ)
    (hfirst : A.IsTerminal (stoppedHistoryFrom policy current first).1)
    (hsecond : A.IsTerminal (stoppedHistoryFrom policy current second).1) :
    stoppedHistoryFrom policy current first =
      stoppedHistoryFrom policy current second := by
  rcases Nat.le_total first second with hle | hle
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact
      (stopped_history_from_add_of_terminal
        policy current first extra hfirst).symm
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact
      stopped_history_from_add_of_terminal
        policy current second extra hsecond

/-- From the empty history, a nonterminal result has length exactly `fuel`. -/
theorem stopped_history_terminal_or_length_eq
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (fuel : ℕ) :
    A.IsTerminal (stoppedHistory policy fuel).1 ∨
      (stoppedHistory policy fuel).2.length = fuel := by
  rcases stopped_history_from_terminal_or_length_eq policy
      (HistoryFrom.nil A start) fuel with hterminal | hlength
  · exact Or.inl hterminal
  · exact Or.inr (by simpa [stoppedHistory, HistoryFrom.nil] using hlength)

end Arena

namespace ExtensiveGame

variable {N U : Type*}

/-- Return the terminal payoff vector reached by a stopped execution.

If the available fuel ends at a nonterminal state, return `none`; in
particular, arbitrary payoffs stored at nonterminal Arena states are never
reported as game outcomes. -/
def stoppedPayoff
    (G : ExtensiveGame N U)
    [(s : G.State) → Decidable (G.isTerminal s)]
    (policy : G.toArena.HistoryPolicy G.init) (fuel : ℕ) :
    Option (N → U) :=
  let result := G.toArena.stoppedHistory policy fuel
  if G.isTerminal result.1 then some (G.payoff result.1) else none

theorem stopped_payoff_eq_some_of_terminal
    (G : ExtensiveGame N U)
    [(s : G.State) → Decidable (G.isTerminal s)]
    (policy : G.toArena.HistoryPolicy G.init) (fuel : ℕ)
    (hterminal :
      G.isTerminal (G.toArena.stoppedHistory policy fuel).1) :
    G.stoppedPayoff policy fuel =
      some (G.payoff (G.toArena.stoppedHistory policy fuel).1) := by
  simp [stoppedPayoff, hterminal]

theorem stopped_payoff_eq_none_of_not_terminal
    (G : ExtensiveGame N U)
    [(s : G.State) → Decidable (G.isTerminal s)]
    (policy : G.toArena.HistoryPolicy G.init) (fuel : ℕ)
    (hterminal :
      ¬ G.isTerminal (G.toArena.stoppedHistory policy fuel).1) :
    G.stoppedPayoff policy fuel = none := by
  simp [stoppedPayoff, hterminal]

/-- Once both fuel bounds reach a terminal state, they return the same payoff. -/
theorem stopped_payoff_eq_of_terminal
    (G : ExtensiveGame N U)
    [(s : G.State) → Decidable (G.isTerminal s)]
    (policy : G.toArena.HistoryPolicy G.init) (first second : ℕ)
    (hfirst :
      G.isTerminal (G.toArena.stoppedHistory policy first).1)
    (hsecond :
      G.isTerminal (G.toArena.stoppedHistory policy second).1) :
    G.stoppedPayoff policy first = G.stoppedPayoff policy second := by
  unfold stoppedPayoff Arena.stoppedHistory
  rw [Arena.stopped_history_from_eq_of_terminal
    policy _ first second hfirst hsecond]

end ExtensiveGame

/-! ### Regression example: a terminal action is never requested -/

namespace Examples.TerminalStoppedExecution

/-- A root with a single action leading to a terminal state with no actions. -/
inductive State
  | root
  | terminal

/-- The one-step arena whose terminal state has an empty action type. -/
def arena : Arena where
  State := State
  Action
    | .root => PUnit
    | .terminal => PEmpty
  next
    | .root, _ => .terminal

/-- A policy that supplies the unique action at the nonterminal root. -/
def policy : arena.HistoryPolicy State.root :=
  fun current hnonterminal => by
    cases h : current.1 with
    | root =>
        exact PUnit.unit
    | terminal =>
        have hterminal : arena.IsTerminal current.1 := by
          rw [h]
          exact ⟨fun action => nomatch action⟩
        exact (hnonterminal hterminal).elim

local instance terminalDecidable :
    (s : arena.State) → Decidable (arena.IsTerminal s) :=
  fun s =>
    match s with
    | .root =>
        isFalse fun hterminal =>
          hterminal.false PUnit.unit
    | .terminal =>
        isTrue ⟨fun action => nomatch action⟩

/-- One unit of fuel reaches the terminal state. -/
theorem one_step_reaches_terminal :
    (arena.stoppedHistory policy 1).1 = State.terminal := by
  have hroot :
      ¬ arena.IsTerminal
        (Arena.HistoryFrom.nil arena State.root).1 := by
    intro hterminal
    exact hterminal.false PUnit.unit
  rw [Arena.stoppedHistory,
    arena.stopped_history_from_succ_of_not_terminal
      policy (Arena.HistoryFrom.nil arena State.root) 0 hroot]
  rfl

/-- Additional fuel cannot move an execution beyond a terminal state. -/
theorem extra_fuel_does_not_move :
    arena.stoppedHistory policy 5 = arena.stoppedHistory policy 1 := by
  have hterminal : arena.IsTerminal (arena.stoppedHistory policy 1).1 := by
    rw [one_step_reaches_terminal]
    change IsEmpty PEmpty
    exact ⟨fun action => nomatch action⟩
  simpa using
    arena.stopped_history_from_add_of_terminal
      policy (Arena.HistoryFrom.nil arena State.root) 1 4 hterminal

end Examples.TerminalStoppedExecution
