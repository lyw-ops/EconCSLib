/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled

/-!
# General payoff-free controlled well-formedness

Represented-information and mover-coherence certificates that require neither
finite action/information carriers nor a structural history-length bound.
`Finite` and `Recall` depend on this leaf without acquiring each other's
assumptions or execution infrastructure.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*} {G : ControlledObservedGame N}

/-- A concrete decision history representing an abstract information state. -/
structure DecisionInfoWitness
    (G : ControlledObservedGame N) (i : N)
    (information : G.InfoState i) where
  /-- Representing complete history. -/
  history : G.base.History
  /-- The selected player moves at the endpoint. -/
  mover : G.base.mover history.1 = some i
  /-- The history represents the requested information state. -/
  infoAt_eq : G.infoAt history i mover = information

/-- Every declared information state is represented by a player decision. -/
def AllDecisionInfoRepresented
    (G : ControlledObservedGame N) : Prop :=
  ∀ (i : N) (information : G.InfoState i),
    Nonempty (G.DecisionInfoWitness i information)

/-- Every player-labelled history has a nonempty legal-action type. -/
def DecisionMoverCoherent
    (G : ControlledObservedGame N) : Prop :=
  ∀ (history : G.base.History) (i : N),
    G.base.mover history.1 = some i →
      Nonempty (G.base.Action history.1)

/-- Mover coherence is exactly terminal-mover normalization on complete
histories reachable from `G.base.init`.

This theorem does not normalize every ambient Arena state: `G.base.History`
contains precisely the occurrence-sensitive histories reachable from the
controlled game's initial state. -/
theorem decisionMoverCoherent_iff_terminal_mover_eq_none_on_histories
    (G : ControlledObservedGame N) :
    G.DecisionMoverCoherent ↔
      ∀ history : G.base.History,
        G.base.isTerminal history.1 →
          G.base.mover history.1 = none := by
  constructor
  · intro hcoherent history hterminal
    cases hmover : G.base.mover history.1 with
    | none => rfl
    | some i =>
        have haction := hcoherent history i hmover
        exact ((not_nonempty_iff.mpr hterminal) haction).elim
  · intro hnormalized history i hmover
    classical
    by_contra hnonempty
    have hterminal : G.base.isTerminal history.1 :=
      not_nonempty_iff.mp hnonempty
    have hnone := hnormalized history hterminal
    rw [hmover] at hnone
    simp at hnone

namespace AllDecisionInfoRepresented

/-- Represented coherent information has a legal abstract action. -/
theorem nonempty_infoAction
    (hrepresented : G.AllDecisionInfoRepresented)
    (hcoherent : G.DecisionMoverCoherent)
    (i : N) (information : G.InfoState i) :
    Nonempty (G.InfoAction i information) := by
  rcases hrepresented i information with ⟨witness⟩
  have haction := hcoherent witness.history i witness.mover
  have habstract :=
    haction.map
      (G.actionEquiv witness.history i witness.mover).symm
  simpa [witness.infoAt_eq] using habstract

/-- Represented coherent information makes each pure-strategy carrier
inhabited. -/
theorem nonempty_pureStrategy
    (hrepresented : G.AllDecisionInfoRepresented)
    (hcoherent : G.DecisionMoverCoherent)
    (i : N) :
    Nonempty (G.PureStrategy i) := by
  classical
  exact
    ⟨fun information =>
      Classical.choice
        (hrepresented.nonempty_infoAction
          hcoherent i information)⟩

/-- Represented coherent information makes the pure-profile carrier
inhabited. -/
theorem nonempty_pureProfile
    (hrepresented : G.AllDecisionInfoRepresented)
    (hcoherent : G.DecisionMoverCoherent) :
    Nonempty G.PureProfile := by
  classical
  exact
    ⟨fun i =>
      Classical.choice
        (hrepresented.nonempty_pureStrategy hcoherent i)⟩

end AllDecisionInfoRepresented

end ExtensiveGame.ControlledObservedGame
