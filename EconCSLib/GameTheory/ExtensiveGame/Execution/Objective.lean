/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic
import EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay
import Mathlib.Data.Nat.Find

/-!
# Terminal and complete-path objectives

This module separates EFG dynamics from outcome interpretation.

* A terminal outcome is indexed by a complete terminal history, so it can
  distinguish two routes that merge into one endpoint state.
* A path outcome is an arbitrary function of a complete legal play.
* A terminal outcome induces an `Option`-valued path outcome without assigning
  an invented value to nonterminating plays.
* Under an explicit all-play termination certificate, the same terminal
  outcome induces a total path outcome.

Utilities and preferences are intentionally not stored here. They are attached
later through `GameForm`, `LawGameForm`, or `ContinuationGameForm`.

## Main definitions

* `Arena.TerminalHistoryFrom`.
* `Arena.TerminalOutcome`.
* `Arena.PathOutcomeFromHistory` and `Arena.PathOutcome`.
* `Arena.TerminalOutcome.toPartialPathOutcome`.
* `Arena.TerminalOutcome.toPathOutcome`.
* `ExtensiveGame.terminalPayoffOutcome`.
-/

namespace Arena

variable {A : Arena} {start : A.State}

/-- A complete terminal history from `start`. -/
abbrev TerminalHistoryFrom (A : Arena) (start : A.State) :=
  {history : A.HistoryFrom start // A.IsTerminal history.1}

/-- A history-sensitive terminal outcome. -/
abbrev TerminalOutcome (A : Arena) (start : A.State)
    (Outcome : Type*) :=
  A.TerminalHistoryFrom start → Outcome

/-- An outcome depending on a complete play from an arbitrary absolute
history. -/
abbrev PathOutcomeFromHistory (A : Arena) {start : A.State}
    (current : A.HistoryFrom start) (Outcome : Type*) :=
  A.CompletePlayFromHistory current → Outcome

/-- An outcome depending on a complete play from an Arena root. -/
abbrev PathOutcome (A : Arena) (start : A.State)
    (Outcome : Type*) :=
  A.CompletePlayFrom start → Outcome

namespace PathOutcomeFromHistory

variable {Outcome : Type*}

/-- Rebase an objective already defined on an absolute tail at `current` onto a
future play rooted at the current endpoint.

`splice` attaches the already accumulated absolute history to every future
coordinate. It does not replay root coordinates preceding `current`; use
`PathOutcome.afterHistory` to restrict an arbitrary root objective. -/
def rebaseTailAt
    (current : A.HistoryFrom start)
    (outcome : A.PathOutcomeFromHistory current Outcome) :
    A.PathOutcome current.1 Outcome :=
  fun future =>
    outcome (CompletePlayFromHistory.splice current future)

@[simp]
theorem rebaseTailAt_apply
    (current : A.HistoryFrom start)
    (outcome : A.PathOutcomeFromHistory current Outcome)
    (future : A.CompletePlayFrom current.1) :
    rebaseTailAt current outcome future =
      outcome
        (CompletePlayFromHistory.splice current future) :=
  rfl

end PathOutcomeFromHistory

namespace PathOutcome

variable {Outcome : Type*}

/-- Restrict an arbitrary root complete-play objective after one accumulated
absolute history.

`resume` replays every prefix coordinate before following the future, so
objectives depending on the root clock or earlier visits retain their original
meaning. -/
def afterHistory
    (outcome : A.PathOutcome start Outcome)
    (current : A.HistoryFrom start) :
    A.PathOutcome current.1 Outcome :=
  fun future =>
    outcome (CompletePlayFromHistory.resume current future)

@[simp]
theorem afterHistory_apply
    (outcome : A.PathOutcome start Outcome)
    (current : A.HistoryFrom start)
    (future : A.CompletePlayFrom current.1) :
    outcome.afterHistory current future =
      outcome (CompletePlayFromHistory.resume current future) :=
  rfl

end PathOutcome

namespace CompletePlayFromHistory

variable {current : A.HistoryFrom start}

/-- The least terminal coordinate of an eventually terminating complete
play. -/
noncomputable def terminalIndex
    (play : A.CompletePlayFromHistory current)
    (hterminates : play.EventuallyTerminates) : ℕ :=
  by
    classical
    exact Nat.find hterminates

/-- The selected terminal coordinate is terminal. -/
theorem terminalIndex_spec
    (play : A.CompletePlayFromHistory current)
    (hterminates : play.EventuallyTerminates) :
    A.IsTerminal
      (play.historyAt (play.terminalIndex hterminates)).1 :=
  by
    classical
    exact Nat.find_spec hterminates

/-- The first terminal complete history of an eventually terminating play. -/
noncomputable def terminalHistory
    (play : A.CompletePlayFromHistory current)
    (hterminates : play.EventuallyTerminates) :
    A.TerminalHistoryFrom start :=
  ⟨play.historyAt (play.terminalIndex hterminates),
    play.terminalIndex_spec hterminates⟩

@[simp]
theorem terminalHistory_val
    (play : A.CompletePlayFromHistory current)
    (hterminates : play.EventuallyTerminates) :
    (play.terminalHistory hterminates).1 =
      play.historyAt (play.terminalIndex hterminates) :=
  rfl

end CompletePlayFromHistory

namespace TerminalOutcome

variable {Outcome : Type*}

/-- Evaluate a terminal outcome on an eventually terminating play. -/
noncomputable def evaluate
    (outcome : A.TerminalOutcome start Outcome)
    (play : A.CompletePlayFrom start)
    (hterminates : play.EventuallyTerminates) :
    Outcome :=
  outcome (play.terminalHistory hterminates)

/-- Regard a terminal outcome as an `Option`-valued path outcome.

Nonterminating plays receive `none`; no artificial terminal utility is
invented. -/
noncomputable def toPartialPathOutcome
    (outcome : A.TerminalOutcome start Outcome) :
    A.PathOutcome start (Option Outcome) := by
  classical
  exact fun play =>
    if hterminates : play.EventuallyTerminates then
      some (outcome.evaluate play hterminates)
    else
      none

/-- A terminating play receives its terminal outcome in the partial path
semantics. -/
theorem toPartialPathOutcome_eq_some
    (outcome : A.TerminalOutcome start Outcome)
    (play : A.CompletePlayFrom start)
    (hterminates : play.EventuallyTerminates) :
    outcome.toPartialPathOutcome play =
      some (outcome.evaluate play hterminates) := by
  simp [toPartialPathOutcome, hterminates]

/-- A nonterminating play receives no terminal outcome. -/
theorem toPartialPathOutcome_eq_none
    (outcome : A.TerminalOutcome start Outcome)
    (play : A.CompletePlayFrom start)
    (hnever : ¬ play.EventuallyTerminates) :
    outcome.toPartialPathOutcome play = none := by
  simp [toPartialPathOutcome, hnever]

/-- Under an explicit all-play termination certificate, a terminal outcome is
a total path outcome. -/
noncomputable def toPathOutcome
    (outcome : A.TerminalOutcome start Outcome)
    (hterminates :
      ∀ play : A.CompletePlayFrom start,
        play.EventuallyTerminates) :
    A.PathOutcome start Outcome :=
  fun play =>
    outcome.evaluate play (hterminates play)

end TerminalOutcome

end Arena

namespace ControlledGame

variable {N : Type*}

/-- Terminal complete histories of a payoff-free controlled game. -/
abbrev TerminalHistory (G : ControlledGame N) :=
  G.toArena.TerminalHistoryFrom G.init

/-- A history-sensitive terminal outcome on a payoff-free controlled game. -/
abbrev TerminalOutcome (G : ControlledGame N) (Outcome : Type*) :=
  G.toArena.TerminalOutcome G.init Outcome

/-- A complete-path outcome on a payoff-free controlled game. -/
abbrev PathOutcome (G : ControlledGame N) (Outcome : Type*) :=
  G.toArena.PathOutcome G.init Outcome

end ControlledGame

namespace ExtensiveGame

variable {N U : Type*}

/-- The existing endpoint-state payoff interpreted as a history-indexed
terminal outcome. -/
def terminalPayoffOutcome (G : ExtensiveGame N U) :
    G.toArena.TerminalOutcome G.init (N → U) :=
  fun history => G.payoff history.1.1

@[simp]
theorem terminalPayoffOutcome_apply
    (G : ExtensiveGame N U)
    (history : G.toArena.TerminalHistoryFrom G.init) :
    G.terminalPayoffOutcome history =
      G.payoff history.1.1 :=
  rfl

end ExtensiveGame
