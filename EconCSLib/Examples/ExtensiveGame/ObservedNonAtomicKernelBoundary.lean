/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.ObservedChanceMeasurableUncountableBoundary
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# A genuinely non-atomic observed-EFG behavioral law

This regression reuses the explicit uncountable complete-history model whose
unique player chooses a real number at the root.  It replaces the old
`PMF ℝ` behavioral law by unit-interval volume, represented as a measurable
kernel on the abstract action space `Set.Icc 0 1`.

The unit-interval action is realized as its underlying real action in the
existing dependent root action fiber.  The compiled concrete bundle law is
therefore the pushforward of unit-interval volume.  It is proved not to equal
`PMF.toMeasure p` for any PMF on the legal history/action bundle.

Thus the example crosses the stochastic, rather than merely carrier-size,
boundary: the chosen action law itself is non-atomic.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Examples.ObservedNonAtomicKernelBoundary

open ExtensiveGame
open MeasurableKernelArena

open ObservedChanceMeasurableUncountableBoundary

abbrev History :=
  ObservedChanceMeasurableUncountableBoundary.History
abbrev HistoryAction :=
  ObservedChanceMeasurableUncountableBoundary.HistoryAction
noncomputable abbrev AnalyticArena :=
  ObservedChanceMeasurableUncountableBoundary.AnalyticArena

local instance : MeasurableSpace History :=
  ObservedChanceMeasurableUncountableBoundary.historyMeasurable

local instance : MeasurableSpace HistoryAction :=
  ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable

local instance : MeasurableSingletonClass HistoryAction where
  measurableSet_singleton bundle := by
    refine
      ⟨({ObservedChanceMeasurableUncountableBoundary.historyActionEquiv
          bundle} : Set ℝ),
        measurableSet_singleton _, ?_⟩
    ext candidate
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact
      ObservedChanceMeasurableUncountableBoundary.historyActionEquiv.injective.eq_iff

/-- Coerce an abstract unit-interval action to the real action carrier used by
the existing realization kernel. -/
def realizationInput (time : ℕ) :
    AnalyticArena.EventPrefix time × Set.Icc (0 : ℝ) 1 →
      AnalyticArena.EventPrefix time × ℝ :=
  fun input => (input.1, input.2.1)

theorem realizationInput_measurable (time : ℕ) :
    Measurable (realizationInput time) :=
  Measurable.prod measurable_fst
    (measurable_subtype_coe.comp measurable_snd)

/-- Reuse the existing history-dependent real-action realization by measurable
comap along the unit-interval inclusion. -/
noncomputable def realizationKernel (time : ℕ) :
    Kernel
      (AnalyticArena.EventPrefix time × Set.Icc (0 : ℝ) 1)
      AnalyticArena.ActionBundle :=
  Kernel.comap
    (ObservedChanceMeasurableUncountableBoundary.realizationKernel time)
    (realizationInput time)
    (realizationInput_measurable time)

instance realizationKernel_isSFinite (time : ℕ) :
    IsSFiniteKernel (realizationKernel time) := by
  letI :
      IsSFiniteKernel
        (ObservedChanceMeasurableUncountableBoundary.realizationKernel
          time) :=
    ObservedChanceMeasurableUncountableBoundary.realization.kernel_isSFinite
      time
  unfold realizationKernel
  infer_instance

@[simp]
theorem realizationKernel_apply_nonterminal
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (action : Set.Icc (0 : ℝ) 1)
    (hnonterminal :
      ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1) :
    realizationKernel time (events, action) =
      Measure.dirac
        (ObservedChanceMeasurableUncountableBoundary.historyActionDecode
          action.1) := by
  change
    ObservedChanceMeasurableUncountableBoundary.realizationKernel
        time (events, action.1) =
      Measure.dirac
        (ObservedChanceMeasurableUncountableBoundary.historyActionDecode
          action.1)
  exact
    ObservedChanceMeasurableUncountableBoundary.realizationKernel_apply_nonterminal
      time events action.1 hnonterminal

@[simp]
theorem realizationKernel_apply_terminal
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (action : Set.Icc (0 : ℝ) 1)
    (hterminal :
      ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1) :
    realizationKernel time (events, action) = 0 := by
  change
    ObservedChanceMeasurableUncountableBoundary.realizationKernel
      time (events, action.1) = 0
  exact
    ObservedChanceMeasurableUncountableBoundary.realizationKernel_apply_terminal
      time events action.1 hterminal

/-- Fixed realization of unit-interval abstract actions as real concrete
actions. -/
noncomputable def realization :
    EventInformation.ActionRealization
      ObservedChanceMeasurableUncountableBoundary.eventInformation where
  AbstractAction := fun _ => Set.Icc (0 : ℝ) 1
  abstractActionMeasurable := fun _ => inferInstance
  kernel := realizationKernel
  kernel_isSFinite := by
    intro time
    infer_instance

/-- Unit-interval volume at root information and zero mass at terminal
information. -/
noncomputable def abstractMeasure :
    Bool → Measure (Set.Icc (0 : ℝ) 1)
  | false => volume
  | true => 0

/-- Measurable information-indexed non-atomic action kernel. -/
noncomputable def abstractKernel :
    Kernel Bool (Set.Icc (0 : ℝ) 1) :=
  Kernel.ofFunOfCountable abstractMeasure

@[simp]
theorem abstractKernel_false :
    abstractKernel false =
      (volume : Measure (Set.Icc (0 : ℝ) 1)) :=
  rfl

@[simp]
theorem abstractKernel_true :
    abstractKernel true = 0 :=
  rfl

instance abstractKernel_isFinite :
    IsFiniteKernel abstractKernel := by
  refine ⟨⟨1, ENNReal.one_lt_top, ?_⟩⟩
  intro information
  cases information
  · rw [abstractKernel_false]
    exact le_of_eq measure_univ
  · rw [abstractKernel_true]
    simp

/-- A terminal complete history has terminal information. -/
theorem historyInformation_eq_true_of_terminal
    (history : History)
    (hterminal :
      ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        history.1) :
    ObservedChanceMeasurableUncountableBoundary.historyInformation history =
      true := by
  cases hinformation :
      ObservedChanceMeasurableUncountableBoundary.historyInformation history with
  | false =>
      have hroot :
          history.1 = .root :=
        ObservedChanceMeasurableUncountableBoundary.endpoint_root_of_historyInformation_eq_false
          history hinformation
      rw [hroot] at hterminal
      change IsEmpty ℝ at hterminal
      exact (hterminal.false 0).elim
  | true => rfl

/-- The genuinely non-atomic realized policy. -/
noncomputable def policy :
    EventInformation.RealizedActionPolicy realization where
  abstractKernel := fun _ => abstractKernel
  abstractKernel_isSFinite := by
    intro _time
    change IsSFiniteKernel abstractKernel
    letI : IsFiniteKernel abstractKernel :=
      abstractKernel_isFinite
    infer_instance
  terminal_zero := by
    intro _time events hterminal
    change
      abstractKernel
        (ObservedChanceMeasurableUncountableBoundary.historyInformation
          (latestEventState _time events)) =
        0
    rw [
      historyInformation_eq_true_of_terminal
        (latestEventState _time events) hterminal,
      abstractKernel_true]
  nonterminal_isProbability := by
    intro time events hnonterminal
    change
      ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1 at hnonterminal
    change
      IsProbabilityMeasure
        (abstractKernel
          (ObservedChanceMeasurableUncountableBoundary.historyInformation
            (latestEventState time events)))
    have hroot :
        (latestEventState time events).1 = .root := by
      cases hstate : (latestEventState time events).1 with
      | root => rfl
      | terminal =>
          apply (hnonterminal ?_).elim
          rw [hstate]
          change IsEmpty Empty
          exact ⟨Empty.elim⟩
    rw [
      ObservedChanceMeasurableUncountableBoundary.historyInformation_eq_false_of_endpoint_root
        (latestEventState time events) hroot,
      abstractKernel_false]
    infer_instance
  realization_isProbability := by
    intro time events hnonterminal
    change
      ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1 at hnonterminal
    exact Filter.Eventually.of_forall fun action => by
      change
        IsProbabilityMeasure
          (realizationKernel time (events, action))
      rw [
        realizationKernel_apply_nonterminal
          time events action hnonterminal]
      constructor
      exact Measure.dirac_apply_of_mem (Set.mem_univ _)
  realization_legal := by
    intro time events hnonterminal
    change
      ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1 at hnonterminal
    have hendpoint :
        (latestEventState time events).1 = .root := by
      cases hstate : (latestEventState time events).1 with
      | root => rfl
      | terminal =>
          exact
            (hnonterminal (by
              rw [hstate]
              change IsEmpty Empty
              exact ⟨Empty.elim⟩)).elim
    have hroot :
        latestEventState time events =
          ObservedChanceMeasurableUncountableBoundary.rootHistory :=
      ObservedChanceMeasurableUncountableBoundary.eq_rootHistory_of_endpoint_root
        (latestEventState time events) hendpoint
    change
      ∀ᵐ stateAction
          ∂(abstractKernel
              (ObservedChanceMeasurableUncountableBoundary.historyInformation
                (latestEventState time events))).bind
            (Kernel.sectR
              (realizationKernel time) events),
        stateAction ∈
          AnalyticArena.actionFiber
            (latestEventState time events)
    letI : IsProbabilityMeasure
        (abstractKernel
          (ObservedChanceMeasurableUncountableBoundary.historyInformation
            (latestEventState time events))) := by
      rw [
        ObservedChanceMeasurableUncountableBoundary.historyInformation_eq_false_of_endpoint_root
          (latestEventState time events) hendpoint,
        abstractKernel_false]
      infer_instance
    apply
      MeasurableKernelArena.EventInformation.RealizedActionPolicy.ae_bind_mem_actionFiber_of_ae_mass_one
        (abstractKernel
          (ObservedChanceMeasurableUncountableBoundary.historyInformation
            (latestEventState time events)))
        (Kernel.sectR (realizationKernel time) events)
        (latestEventState time events)
    · exact Filter.Eventually.of_forall fun action => by
        rw [
          Kernel.sectR_apply,
          realizationKernel_apply_nonterminal
            time events action hnonterminal]
        constructor
        exact Measure.dirac_apply_of_mem (Set.mem_univ _)
    · exact Filter.Eventually.of_forall fun action => by
        rw [
          Kernel.sectR_apply,
          realizationKernel_apply_nonterminal
            time events action hnonterminal]
        apply Measure.dirac_apply_of_mem
        change
          (ObservedChanceMeasurableUncountableBoundary.historyActionDecode
            action.1).1 =
            latestEventState time events
        rw [
          ObservedChanceMeasurableUncountableBoundary.historyActionDecode_fst,
          hroot]

/-- The observed structural presentation with no chance nodes.  Its fixed
chance kernel is zero because the chance branch is unreachable. -/
noncomputable def presentation :
    ObservedChanceMeasurableUncountableBoundary.game.observed.MeasurableKernelPresentation
      ObservedChanceMeasurableUncountableBoundary.measurableHistoryModel where
  information :=
    ObservedChanceMeasurableUncountableBoundary.eventInformation
  realization := realization
  playerInformation := fun _time _information => false
  player_informationAt := by
    intro time events i hmover
    have hroot :
        (latestEventState time events).1 = .root := by
      cases hstate : (latestEventState time events).1 with
      | root => rfl
      | terminal =>
          change
            ObservedChanceMeasurableUncountableBoundary.nodeMover _ =
              some i at hmover
          rw [hstate] at hmover
          contradiction
    change
      ObservedChanceMeasurableUncountableBoundary.historyInformation
          (latestEventState time events) =
        false
    exact
      ObservedChanceMeasurableUncountableBoundary.historyInformation_eq_false_of_endpoint_root
        (latestEventState time events) hroot
  chanceKernel := fun _time => 0
  chanceKernel_isSFinite := by
    intro _time
    infer_instance

/-- The non-atomic policy packaged as a behavioral profile.  Chance
consistency is vacuous only because the strict regression has no chance
prefixes. -/
noncomputable def profile :
    presentation.KernelBehavioralProfile where
  policy := policy
  chance_eq := by
    intro time events hnonterminal hmover
    have hroot :
        (latestEventState time events).1 = .root := by
      cases hstate : (latestEventState time events).1 with
      | root => rfl
      | terminal =>
          exact
            (hnonterminal (by
              rw [hstate]
              change IsEmpty Empty
              exact ⟨Empty.elim⟩)).elim
    change
      ObservedChanceMeasurableUncountableBoundary.nodeMover _ =
        none at hmover
    rw [hroot] at hmover
    contradiction

/-- Nature, rather than a player, controls the otherwise identical real-action
root. -/
def chanceMover :
    ObservedChanceMeasurableUncountableBoundary.Node →
      Option Unit
  | .root => none
  | .terminal => none

/-- Structural extensive game for the strict non-atomic chance regression. -/
def chanceBase : ExtensiveGame Unit Unit where
  State := ObservedChanceMeasurableUncountableBoundary.Node
  Action := ObservedChanceMeasurableUncountableBoundary.nodeAction
  next := ObservedChanceMeasurableUncountableBoundary.nodeNext
  init := .root
  mover := chanceMover
  payoff := fun _ _ => ()

/-- No history in `chanceBase` is player-controlled. -/
theorem chanceBase_mover_ne_some
    (history :
      chanceBase.toArena.HistoryFrom chanceBase.init)
    (i : Unit) :
    chanceBase.mover history.1 ≠ some i := by
  cases i
  cases history.1 <;> simp [chanceBase, chanceMover]

/-- Observed structural game whose sole nonterminal node is a chance node.
The player information/action fields are unreachable structural data. -/
def chanceObserved : ObservedGame Unit Unit where
  base := chanceBase
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := fun _ _ => rfl
  InfoState := fun _ => Unit
  infoObserve := fun _ _ => ()
  infoAt := fun _history _i _hmover => ()
  infoAt_observe := fun _history _i _hmover => rfl
  InfoAction := fun _ _ => ℝ
  actionEquiv := by
    intro history i hmover
    exact
      (chanceBase_mover_ne_some history i hmover).elim
  IsDesignatedContinuationRoot := fun _ => True
  init_isDesignatedContinuationRoot := trivial

/-- The chance-controlled game has definitionally the same history dynamics
and therefore reuses the explicit measurable history model. -/
noncomputable def chanceHistoryModel :
    chanceObserved.MeasurableHistoryModel := by
  exact
    { historyMeasurable :=
        ObservedChanceMeasurableUncountableBoundary.historyMeasurable
      historyActionMeasurable :=
        ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
      stateProjection_measurable :=
        ObservedChanceMeasurableUncountableBoundary.stateProjection_measurable
      appendHistory_measurable :=
        ObservedChanceMeasurableUncountableBoundary.appendHistory_measurable
      transition :=
        Kernel.deterministic
          (ObservedGame.appendHistory chanceObserved)
          ObservedChanceMeasurableUncountableBoundary.appendHistory_measurable
      transition_isMarkov := by
        infer_instance
      transition_apply := by
        intro historyAction
        rw [Kernel.deterministic_apply]
        rw [PMF.toMeasure_pure]
      terminalSet_measurable :=
        ObservedChanceMeasurableUncountableBoundary.terminalSet_measurable
      singleton_measurable :=
        ObservedChanceMeasurableUncountableBoundary.singleton_measurable }

/-- Fixed non-atomic chance presentation.  The same unit-interval realized
kernel is now structural chance data rather than a player's strategic law. -/
noncomputable def chancePresentation :
    chanceObserved.MeasurableKernelPresentation
      chanceHistoryModel where
  information :=
    ObservedChanceMeasurableUncountableBoundary.eventInformation
  realization := realization
  playerInformation := fun _time _information => false
  player_informationAt := by
    intro _time events i hmover
    exact
      (chanceBase_mover_ne_some
        (latestEventState _time events) i hmover).elim
  chanceKernel := policy.realizedKernel
  chanceKernel_isSFinite := by
    intro time
    exact
      EventInformation.RealizedActionPolicy.realizedKernel_isSFinite
        policy time

/-- The strict chance profile uses exactly the fixed non-atomic nature law. -/
noncomputable def chanceProfile :
    chancePresentation.KernelBehavioralProfile where
  policy := policy
  chance_eq := by
    intro _time _events _hnonterminal _hmover
    rfl

/-- The concrete initial event prefix used to witness that both strict
regression branches are inhabited. -/
noncomputable def rootPrefix :
    AnalyticArena.EventPrefix 0 :=
  fun _index =>
    AnalyticArena.initialEvent
      ObservedChanceMeasurableUncountableBoundary.rootHistory

@[simp]
theorem latestEventState_rootPrefix :
    latestEventState 0 rootPrefix =
      ObservedChanceMeasurableUncountableBoundary.rootHistory :=
  rfl

/-- The represented root is genuinely nonterminal. -/
theorem root_nonterminal :
    ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
      (latestEventState 0 rootPrefix).1 := by
  change ¬ IsEmpty ℝ
  intro hempty
  exact hempty.false 0

/-- The strict player regression really has a player-controlled root. -/
theorem player_root_mover :
    ObservedChanceMeasurableUncountableBoundary.game.observed.base.mover
        (latestEventState 0 rootPrefix).1 =
      some () :=
  rfl

/-- The strict chance regression really has a chance-controlled root. -/
theorem chance_root_mover :
    chanceObserved.base.mover
        (latestEventState 0 rootPrefix).1 =
      none :=
  rfl

/-- Measurable injection from unit-interval actions into legal concrete
history/action bundles. -/
def packageAction (action : Set.Icc (0 : ℝ) 1) :
    HistoryAction :=
  ObservedChanceMeasurableUncountableBoundary.historyActionDecode action.1

theorem packageAction_measurable :
    Measurable packageAction :=
  ObservedChanceMeasurableUncountableBoundary.historyActionMeasurableEquiv.symm.measurable.comp
    measurable_subtype_coe

theorem packageAction_injective :
    Function.Injective packageAction := by
  intro first second heq
  apply Subtype.ext
  have hcode :=
    congrArg
      ObservedChanceMeasurableUncountableBoundary.historyActionCode heq
  simpa [packageAction] using hcode

/-- The compiled concrete root action-bundle law. -/
noncomputable def concreteRootLaw :
    Measure HistoryAction :=
  (volume : Measure (Set.Icc (0 : ℝ) 1)).map packageAction

/-- At every represented nonterminal prefix, compilation preserves the
non-atomic unit-interval law exactly. -/
theorem compiled_player_kernel_exact
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (hnonterminal :
      ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1) :
    profile.compiledPolicy.kernel time events =
      concreteRootLaw := by
  rw [
    ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.compiledPolicy_kernel,
    EventInformation.RealizedActionPolicy.realizedKernel_apply]
  change
    (abstractKernel
        (ObservedChanceMeasurableUncountableBoundary.historyInformation
          (latestEventState time events))).bind
      (fun action =>
        realizationKernel time (events, action)) =
      concreteRootLaw
  have hroot :
      (latestEventState time events).1 = .root := by
    cases hstate : (latestEventState time events).1 with
    | root => rfl
    | terminal =>
        exact
          (hnonterminal (by
            rw [hstate]
            change IsEmpty Empty
            exact ⟨Empty.elim⟩)).elim
  rw [
    ObservedChanceMeasurableUncountableBoundary.historyInformation_eq_false_of_endpoint_root
      (latestEventState time events) hroot,
    abstractKernel_false]
  simp_rw [
    realizationKernel_apply_nonterminal
      time events _ hnonterminal]
  exact
    Measure.bind_dirac_eq_map
      (volume : Measure (Set.Icc (0 : ℝ) 1))
      packageAction_measurable

/-- The same strict law is realized at the genuinely chance-controlled root.
The `hmover` premise rules out a vacuous player-only regression. -/
theorem compiled_chance_kernel_exact
    (time : ℕ)
    (events : chanceHistoryModel.toArena.EventPrefix time)
    (hnonterminal :
      ¬ chanceObserved.base.isTerminal
        (latestEventState time events).1)
    (_hmover :
      chanceObserved.base.mover
          (latestEventState time events).1 =
        none) :
    chanceProfile.compiledPolicy.kernel time events =
      concreteRootLaw := by
  change
    profile.compiledPolicy.kernel time events =
      concreteRootLaw
  exact
    compiled_player_kernel_exact
      time events hnonterminal

/-- The inhabited player root has exactly the non-atomic concrete law. -/
theorem compiled_player_root_kernel_exact :
    profile.compiledPolicy.kernel 0 rootPrefix =
      concreteRootLaw :=
  compiled_player_kernel_exact
    0 rootPrefix root_nonterminal

/-- The inhabited chance root has exactly the non-atomic concrete law. -/
theorem compiled_chance_root_kernel_exact :
    chanceProfile.compiledPolicy.kernel 0 rootPrefix =
      concreteRootLaw :=
  compiled_chance_kernel_exact
    0 rootPrefix root_nonterminal chance_root_mover

instance concreteRootLaw_noAtoms :
    NoAtoms concreteRootLaw where
  measure_singleton bundle := by
    rw [
      concreteRootLaw,
      Measure.map_apply
        packageAction_measurable
        (measurableSet_singleton bundle)]
    exact
      Set.Subsingleton.measure_zero
        (by
          intro first hfirst second hsecond
          apply packageAction_injective
          exact hfirst.trans hsecond.symm)
        (volume : Measure (Set.Icc (0 : ℝ) 1))

/-- Every singleton concrete action bundle has probability zero. -/
theorem concreteRootLaw_singleton
    (bundle : HistoryAction) :
    concreteRootLaw {bundle} = 0 :=
  measure_singleton bundle

/-- The compiled root action law is not the measure associated with any PMF
on the legal history/action bundle. -/
theorem no_discretePMF_concreteRootLaw :
    ¬ ∃ p : PMF HistoryAction,
      @PMF.toMeasure
          HistoryAction
          ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
          p =
        concreteRootLaw := by
  rintro ⟨p, hp⟩
  have hsupportOne :
      @PMF.toMeasure
          HistoryAction
          ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
          p p.support =
        1 :=
    (p.toMeasure_apply_eq_one_iff
      p.support_countable.measurableSet).mpr Set.Subset.rfl
  have hsupportZero :
      concreteRootLaw p.support = 0 :=
    p.support_countable.measure_zero concreteRootLaw
  rw [hp, hsupportZero] at hsupportOne
  exact zero_ne_one hsupportOne

/-- Consequently, the compiled player kernel itself has no PMF
representation. -/
theorem no_discretePMF_compiled_player_kernel
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (hnonterminal :
      ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1) :
    ¬ ∃ p : PMF HistoryAction,
      @PMF.toMeasure
          HistoryAction
          ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
          p =
        profile.compiledPolicy.kernel time events := by
  simpa only [compiled_player_kernel_exact time events hnonterminal] using
    no_discretePMF_concreteRootLaw

/-- The strict chance kernel also has no PMF representation. -/
theorem no_discretePMF_compiled_chance_kernel
    (time : ℕ)
    (events : chanceHistoryModel.toArena.EventPrefix time)
    (hnonterminal :
      ¬ chanceObserved.base.isTerminal
        (latestEventState time events).1)
    (hmover :
      chanceObserved.base.mover
          (latestEventState time events).1 =
        none) :
    ¬ ∃ p : PMF HistoryAction,
      @PMF.toMeasure
          HistoryAction
          ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
          p =
        chanceProfile.compiledPolicy.kernel time events := by
  simpa only [
    compiled_chance_kernel_exact
      time events hnonterminal hmover] using
    no_discretePMF_concreteRootLaw

/-- The inhabited player-root kernel has no PMF representation. -/
theorem no_discretePMF_compiled_player_root_kernel :
    ¬ ∃ p : PMF HistoryAction,
      @PMF.toMeasure
          HistoryAction
          ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
          p =
        profile.compiledPolicy.kernel 0 rootPrefix := by
  simpa only [compiled_player_root_kernel_exact] using
    no_discretePMF_concreteRootLaw

/-- The inhabited chance-root kernel has no PMF representation. -/
theorem no_discretePMF_compiled_chance_root_kernel :
    ¬ ∃ p : PMF HistoryAction,
      @PMF.toMeasure
          HistoryAction
          ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
          p =
        chanceProfile.compiledPolicy.kernel 0 rootPrefix := by
  simpa only [compiled_chance_root_kernel_exact] using
    no_discretePMF_concreteRootLaw

/-- The general executor produces a complete joint event-path law for the
non-atomic behavioral profile. -/
noncomputable def eventPathMeasure :
    Measure (ℕ → AnalyticArena.PathEvent) :=
  profile.eventPathMeasure
    ObservedChanceMeasurableUncountableBoundary.rootHistory

/-- The corresponding complete state-path law. -/
noncomputable def statePathMeasure :
    Measure (ℕ → AnalyticArena.State) :=
  profile.statePathMeasure
    ObservedChanceMeasurableUncountableBoundary.rootHistory

end Examples.ObservedNonAtomicKernelBoundary
