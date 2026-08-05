/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Game
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Finite

/-!
# Structural well-formedness and finite-EFG certificates

The general `ObservedGame` carrier intentionally permits unreachable
information states, infinite branching, player labels at terminal endpoints,
and infinite play. This module packages the stronger assumptions required by
finite textbook EFG algorithms without adding a second semantic game record.

`FiniteEFGHypotheses` is structural and representation-aware. It uses a
uniform bound in the complete-history unfolding rather than finite compact
state, and it requires every declared decision information state to be
represented. Finiteness of players and executable decidability assumptions
remain theorem-local because many structural results do not enumerate
players or compute transitions.

## Main definitions

* `ObservedGame.AllDecisionInfoRepresented`.
* `ObservedGame.DecisionMoverCoherent`.
* `ObservedGame.FiniteEFGHypotheses`.

## Main results

* represented coherent information has a nonempty abstract action type;
* coherent fully represented games have inhabited pure contingent plans;
* every play under `FiniteEFGHypotheses` terminates and the unfolding is
  structurally well-founded.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} {G : ObservedGame N U}

/-- Every declared decision information state is represented by an actual
player-controlled complete history. -/
abbrev AllDecisionInfoRepresented
    (G : ObservedGame N U) : Prop :=
  G.toControlledObservedGame.AllDecisionInfoRepresented

/-- Every player-labeled complete history is a genuine decision history with
at least one legal action.

This condition is deliberately not a field of `ExtensiveGame`: terminal
execution ignores mover labels. It is needed when all declared decision
information states are used to form total contingent plans. -/
abbrev DecisionMoverCoherent
    (G : ObservedGame N U) : Prop :=
  G.toControlledObservedGame.DecisionMoverCoherent

/-- The canonical decision-history complete-information presentation has no
ghost decision-information states. -/
theorem completeInformation_allDecisionInfoRepresented
    (base : ExtensiveGame N U) :
    AllDecisionInfoRepresented
      (completeInformation base) := by
  intro i information
  refine ⟨
    { history := information.1
      mover := information.2.1
      nonterminal := information.2.2
      infoAt_eq := ?_ }⟩
  cases information
  rfl

namespace AllDecisionInfoRepresented

/-- A represented information state in a mover-coherent game has at least one
abstract legal action. -/
theorem nonempty_infoAction
    (hrepresented : G.AllDecisionInfoRepresented)
    (hcoherent : G.DecisionMoverCoherent)
    (i : N) (information : G.InfoState i) :
    Nonempty (G.InfoAction i information) :=
  ControlledObservedGame.AllDecisionInfoRepresented.nonempty_infoAction
    hrepresented hcoherent i information

/-- Full representation and mover coherence make every player's total pure
contingent-plan type inhabited. -/
theorem nonempty_pureStrategy
    (hrepresented : G.AllDecisionInfoRepresented)
    (hcoherent : G.DecisionMoverCoherent)
    (i : N) :
    Nonempty (G.PureStrategy i) :=
  ControlledObservedGame.AllDecisionInfoRepresented.nonempty_pureStrategy
    hrepresented hcoherent i

/-- Full representation and mover coherence make the pure-profile type
inhabited, without requiring a finite player type. -/
theorem nonempty_pureProfile
    (hrepresented : G.AllDecisionInfoRepresented)
    (hcoherent : G.DecisionMoverCoherent) :
    Nonempty G.PureProfile :=
  ControlledObservedGame.AllDecisionInfoRepresented.nonempty_pureProfile
    hrepresented hcoherent

end AllDecisionInfoRepresented

/-- A mover-coherent canonical complete-information presentation has an
inhabited pure-profile carrier.

The coherence premise is essential because the unconstrained base game may
attach a player mover label to a terminal state, whose action type is empty.
-/
theorem completeInformation_nonempty_pureProfile
    (base : ExtensiveGame N U)
    (hcoherent :
      (completeInformation base).DecisionMoverCoherent) :
    Nonempty
      (completeInformation base).PureProfile :=
  (completeInformation_allDecisionInfoRepresented
    base).nonempty_pureProfile hcoherent

/-- Reusable structural hypotheses for a finite textbook EFG presentation.

The selected `lengthBound` bounds the legal complete-history unfolding, not
the compact state space. `finiteAction` and `finiteInfoState` are typeclass
certificates stored propositionally and can be installed locally by an
algorithm. Player finiteness, perfect recall, chance laws, preference orders,
and decidable comparisons are intentionally separate. -/
abbrev FiniteEFGHypotheses
    (G : ObservedGame N U) :=
  G.toControlledObservedGame.FiniteEFGHypotheses

namespace FiniteEFGHypotheses

/-- A finite-EFG certificate supplies structural well-foundedness of the
complete-history unfolding. -/
theorem isWellFoundedFrom
    (h : G.FiniteEFGHypotheses) :
    G.base.toArena.IsWellFoundedFrom G.base.init :=
  ControlledObservedGame.FiniteEFGHypotheses.isWellFoundedFrom h

/-- Every complete legal play of a finite-EFG certificate eventually
terminates. -/
theorem eventuallyTerminates
    (h : G.FiniteEFGHypotheses)
    (play :
      G.base.toArena.CompletePlayFrom G.base.init) :
    play.EventuallyTerminates :=
  ControlledObservedGame.FiniteEFGHypotheses.eventuallyTerminates h play

/-- The certificate makes every player's total pure contingent-plan type
inhabited. -/
theorem nonempty_pureStrategy
    (h : G.FiniteEFGHypotheses) (i : N) :
    Nonempty (G.PureStrategy i) :=
  h.allDecisionInfoRepresented.nonempty_pureStrategy
    h.decisionMoverCoherent i

/-- The certificate makes the full pure-profile type inhabited. -/
theorem nonempty_pureProfile
    (h : G.FiniteEFGHypotheses) :
    Nonempty G.PureProfile :=
  ControlledObservedGame.FiniteEFGHypotheses.nonempty_pureProfile h

end FiniteEFGHypotheses

end ExtensiveGame.ObservedGame
