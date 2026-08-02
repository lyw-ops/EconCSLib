/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Length
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.WellFormed

/-!
# Payoff-free finite EFG certificates

Structural finite-EFG hypotheses for `ControlledObservedGame`. General
represented-information and mover-coherence certificates live in
`ControlledInfrastructure.WellFormed`; this leaf adds only the assumptions and
consequences that genuinely require a finite reachable unfolding or a
structural history-length bound.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*} {G : ControlledObservedGame N}

/-! ## Finite structure -/

/-- Structural certificate for a finite payoff-free observed EFG.

The bound applies to the reachable complete-history unfolding, not to the
ambient compact state type. Chance laws, recall, player finiteness, and
objectives are intentionally separate. -/
structure FiniteEFGHypotheses
    (G : ControlledObservedGame N) where
  /-- Uniform bound on legal action occurrences. -/
  lengthBound : ℕ
  /-- Every legal continuation of that length has terminated. -/
  hasLengthBound :
    G.base.toArena.HasLengthBoundFrom
      G.base.init lengthBound
  /-- Each reachable concrete action fiber is finite. -/
  finiteAction :
    ∀ history : G.base.History,
      Finite (G.base.Action history.1)
  /-- Each information-state carrier is finite. -/
  finiteInfoState :
    ∀ i : N, Finite (G.InfoState i)
  /-- No ghost information states occur. -/
  allDecisionInfoRepresented :
    G.AllDecisionInfoRepresented
  /-- Player labels denote genuine decision nodes. -/
  decisionMoverCoherent :
    G.DecisionMoverCoherent

namespace FiniteEFGHypotheses

/-- A finite-EFG certificate makes the history unfolding well-founded. -/
theorem isWellFoundedFrom
    (h : G.FiniteEFGHypotheses) :
    G.base.toArena.IsWellFoundedFrom G.base.init :=
  Arena.HasLengthBoundFrom.isWellFoundedFrom
    h.hasLengthBound

/-- Every complete play under a finite-EFG certificate terminates. -/
theorem eventuallyTerminates
    (h : G.FiniteEFGHypotheses)
    (play : G.base.CompletePlay) :
    play.EventuallyTerminates :=
  Arena.HasLengthBoundAt.eventuallyTerminates
    h.hasLengthBound play

/-- A finite-EFG certificate supplies an inhabited pure-profile carrier. -/
theorem nonempty_pureProfile
    (h : G.FiniteEFGHypotheses) :
    Nonempty G.PureProfile :=
  h.allDecisionInfoRepresented.nonempty_pureProfile
    h.decisionMoverCoherent

end FiniteEFGHypotheses

end ExtensiveGame.ControlledObservedGame
