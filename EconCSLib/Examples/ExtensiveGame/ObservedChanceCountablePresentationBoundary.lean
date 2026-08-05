/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.ObservedChanceKernelBridgeBoundary
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Countable

/-!
# Canonical countable observed-chance presentation regression

This regression instantiates the canonical countable-discrete analytic
presentation on the absent-minded three-rung game.

Unlike the earlier explicit realized-presentation example, no model-specific
information map, realization kernel, abstract kernel, or compilation proof is
written here. The only nontrivial local obligation is countability of complete
histories. It is proved by an exhaustive three-point cover of the acyclic
game. Countability of tagged information, tagged abstract actions, concrete
bundles, and every finite event prefix then follows from the reusable
constructor.

The resulting presentation still merges the recurring original player
information state at the two distinct complete histories and compiles exactly
to the established stopped-history law.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.ObservedChanceCountablePresentationBoundary

open Examples.AbsentMinded
open Examples.ObservedChanceKernelBridgeBoundary
open ExtensiveGame
open MeasurableKernelArena

/-- The unique complete history ending at the terminal rung. -/
def lastHistory :
    base.toArena.HistoryFrom base.init :=
  ⟨Rung.s2, secondDecision.2.snoc ()⟩

/-- Every complete history of the three-rung game is one of its three
prefixes. -/
theorem history_classify
    (history : base.toArena.HistoryFrom base.init) :
    history = firstDecision ∨
      history = secondDecision ∨
      history = lastHistory := by
  rcases history with ⟨state, path⟩
  refine Arena.History.rec
    (motive := fun state path =>
      (⟨state, path⟩ : base.toArena.HistoryFrom base.init) =
          firstDecision ∨
        (⟨state, path⟩ : base.toArena.HistoryFrom base.init) =
            secondDecision ∨
        (⟨state, path⟩ : base.toArena.HistoryFrom base.init) =
          lastHistory)
    ?_ ?_ path
  · exact Or.inl rfl
  · intro state path action ih
    rcases ih with hfirst | hsecond | hlast
    · cases hfirst
      cases action
      exact Or.inr (Or.inl rfl)
    · cases hsecond
      cases action
      exact Or.inr (Or.inr rfl)
    · cases hlast
      exact PEmpty.elim action

/-- A finite cover used only to derive the complete-history countability
instance. -/
def historyCover :
    Fin 3 → base.toArena.HistoryFrom base.init
  | 0 => firstDecision
  | 1 => secondDecision
  | 2 => lastHistory

theorem historyCover_surjective :
    Function.Surjective historyCover := by
  intro history
  rcases history_classify history with hfirst | hsecond | hlast
  · exact ⟨0, hfirst.symm⟩
  · exact ⟨1, hsecond.symm⟩
  · exact ⟨2, hlast.symm⟩

noncomputable instance baseHistoryCountable :
    Countable (base.toArena.HistoryFrom base.init) :=
  historyCover_surjective.countable

noncomputable instance gameHistoryCountable :
    Countable
      (game.observed.base.toArena.HistoryFrom
        game.observed.base.init) := by
  change Countable (base.toArena.HistoryFrom base.init)
  infer_instance

noncomputable instance gameLocalActionCountable
    (history :
      game.observed.base.toArena.HistoryFrom
        game.observed.base.init) :
    Countable (game.observed.base.Action history.1) := by
  change Countable (rungAction history.1)
  cases history.1 <;> simp only [rungAction] <;> infer_instance

noncomputable instance gameInfoStateCountable (i : Fin 1) :
    Countable (game.observed.InfoState i) := by
  change Countable Unit
  infer_instance

noncomputable instance gameInfoActionCountable
    (i : Fin 1) (information : game.observed.InfoState i) :
    Countable (game.observed.InfoAction i information) := by
  change Countable Unit
  infer_instance

/-- The fully automatic countable-discrete analytic presentation of the
absent-minded observed chance game. -/
noncomputable def presentation :
    game.AnalyticPresentation :=
  ExtensiveGame.ObservedChanceGame.CountablePresentation.presentation game

/-- The two recurring player histories use exactly the same canonical
abstract action law because their original information states agree. -/
theorem recurring_player_abstract_law_eq :
    (presentation.toPolicy profile).abstractKernel 0
        (presentation.information.informationAt 0 firstPrefix) =
      (presentation.toPolicy profile).abstractKernel 0
        (presentation.information.informationAt 0 secondPrefix) := by
  exact
    presentation.abstractKernel_eq_of_player_infoAt_eq
      profile 0 firstPrefix secondPrefix 0
      rfl firstPrefix_nonterminal
      rfl secondPrefix_nonterminal
      infoState_recurs

/-- The automatic presentation compiles exactly to the original concrete
history action kernel at every finite event prefix. -/
theorem compiled_kernel_exact
    (time : ℕ)
    (events : game.AnalyticHistoryArena.EventPrefix time) :
      (presentation.toPolicy profile).toEventHistoryActionPolicy.kernel
        time events =
      (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
        game profile).toMeasurable.kernel
        (MeasurableKernelArena.latestEventState time events) :=
  presentation.compiled_kernel profile time events

/-- The automatic presentation recovers the exact old two-step stopped
complete-history law. -/
theorem two_step_state_law_exact :
    Measure.map
        (fun path : ℕ → game.AnalyticHistoryArena.State => path 2)
        (EventHistoryActionPolicy.statePathMeasure
          (presentation.toPolicy profile).toEventHistoryActionPolicy
            (game.observed.base.toArena.historyKernelArena
              game.observed.base.init).toMeasurable_measurableSet_terminalSet
            firstDecision) =
      @PMF.toMeasure
        (game.observed.base.toArena.HistoryFrom
          game.observed.base.init) ⊤
        (game.observed.base.toArena.stochasticHistoryPMFFrom
          (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
            game profile)
          firstDecision 2) :=
  presentation.compiled_finite_state_law
    profile 2 firstDecision

end Examples.ObservedChanceCountablePresentationBoundary
