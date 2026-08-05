/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.ObservedNonAtomicKernelBoundary
import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic

/-!
# Non-countably-supported pure-profile law

The one-player real-action observed game has complete pure profiles equivalent
to `ℝ`. Transporting the Borel measurable space along that equivalence lets
unit-interval volume define an arbitrary-measure pure-profile law.

The law is proved not to be `PMF.toMeasure` of any PMF. This regression tests
that the analytic strategy carrier genuinely crosses the countably supported
boundary rather than merely renaming a discrete law.
-/

open MeasureTheory
open scoped unitInterval

namespace Examples.ArbitraryMeasurePureStrategyBoundary

open ExtensiveGame

abbrev game :=
  ObservedChanceMeasurableUncountableBoundary.observed

/-- Read the sole real action from a complete pure profile. -/
def profileAction (profile : game.PureProfile) : ℝ :=
  profile () ()

/-- Make the constant one-player plan selecting one real action. -/
def profileOfAction (action : ℝ) : game.PureProfile :=
  fun _player _information => action

/-- Complete pure profiles of the one-decision game are equivalent to real
actions. -/
def profileEquiv : game.PureProfile ≃ ℝ where
  toFun := profileAction
  invFun := profileOfAction
  left_inv := by
    intro profile
    funext player information
    cases player
    cases information
    rfl
  right_inv := by
    intro action
    rfl

/-- Read the sole action from one player's pure strategy. -/
def strategyAction (strategy : game.PureStrategy ()) : ℝ :=
  strategy ()

/-- One-player pure strategies are equivalent to real actions. -/
def strategyEquiv : game.PureStrategy () ≃ ℝ where
  toFun := strategyAction
  invFun := fun action _information => action
  left_inv := by
    intro strategy
    funext information
    cases information
    rfl
  right_inv := by
    intro action
    rfl

/-- Borel structure transported from the real action code. -/
@[reducible] def profileMeasurableSpace :
    MeasurableSpace game.PureProfile :=
  (inferInstance : MeasurableSpace ℝ).comap profileEquiv

/-- Borel structure on the sole player's pure strategy. -/
@[reducible] def strategyMeasurableSpace :
    MeasurableSpace (game.PureStrategy ()) :=
  (inferInstance : MeasurableSpace ℝ).comap strategyEquiv

local instance : MeasurableSpace game.PureProfile :=
  profileMeasurableSpace

local instance : MeasurableSpace (game.PureStrategy ()) :=
  strategyMeasurableSpace

/-- The profile coding equivalence is measurable in both directions. -/
def profileMeasurableEquiv : game.PureProfile ≃ᵐ ℝ where
  toEquiv := profileEquiv
  measurable_toFun := comap_measurable profileEquiv
  measurable_invFun := by
    change
      @Measurable ℝ game.PureProfile
        inferInstance profileMeasurableSpace profileEquiv.symm
    unfold profileMeasurableSpace
    rw [measurable_comap_iff]
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      (measurable_id : Measurable (fun action : ℝ => action))

/-- The strategy coding equivalence is measurable in both directions. -/
def strategyMeasurableEquiv :
    game.PureStrategy () ≃ᵐ ℝ where
  toEquiv := strategyEquiv
  measurable_toFun := comap_measurable strategyEquiv
  measurable_invFun := by
    change
      @Measurable ℝ (game.PureStrategy ())
        inferInstance strategyMeasurableSpace strategyEquiv.symm
    unfold strategyMeasurableSpace
    rw [measurable_comap_iff]
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      (measurable_id : Measurable (fun action : ℝ => action))

/-- Explicit measurable model for the dependent pure-strategy carriers. -/
def measurableModel : game.PureProfileMeasurableModel where
  strategyMeasurableSpace := fun player => by
    cases player
    exact strategyMeasurableSpace
  profileMeasurableSpace := profileMeasurableSpace
  coordinate_measurable := by
    intro player
    cases player
    change
      @Measurable game.PureProfile (game.PureStrategy ())
        profileMeasurableSpace strategyMeasurableSpace
        (fun profile => profile ())
    unfold strategyMeasurableSpace
    rw [measurable_comap_iff]
    have heq :
        strategyEquiv ∘ (fun profile : game.PureProfile => profile ()) =
          profileEquiv := by
      rfl
    rw [heq]
    exact comap_measurable profileEquiv

/-- Embed a unit-interval draw as the constant pure profile selecting that
real root action. -/
def profileOfUnitInterval
    (action : Set.Icc (0 : ℝ) 1) : game.PureProfile :=
  profileOfAction action.1

theorem profileOfUnitInterval_measurable :
    Measurable profileOfUnitInterval :=
  profileMeasurableEquiv.symm.measurable.comp measurable_subtype_coe

theorem profileOfUnitInterval_injective :
    Function.Injective profileOfUnitInterval := by
  intro first second heq
  apply Subtype.ext
  exact congrArg profileAction heq

/-- Unit-interval volume as a probability measure. -/
noncomputable def unitIntervalLaw :
    ProbabilityMeasure (Set.Icc (0 : ℝ) 1) :=
  ⟨volume, inferInstance⟩

/-- A genuinely non-countably-supported pure-profile law. -/
noncomputable def profileLaw :
    game.ArbitraryMeasurePureProfileLaw measurableModel :=
  ProbabilityMeasure.map unitIntervalLaw
    profileOfUnitInterval_measurable.aemeasurable

/-- The underlying measure of the non-atomic profile law. -/
noncomputable def profileMeasure : Measure game.PureProfile :=
  @ProbabilityMeasure.toMeasure game.PureProfile
    measurableModel.profileMeasurableSpace profileLaw

local instance : MeasurableSingletonClass game.PureProfile where
  measurableSet_singleton profile := by
    refine
      ⟨({profileEquiv profile} : Set ℝ),
        measurableSet_singleton _, ?_⟩
    ext candidate
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact profileEquiv.injective.eq_iff

instance profileLaw_noAtoms :
    NoAtoms profileMeasure where
  measure_singleton profile := by
    rw [profileMeasure, profileLaw, ProbabilityMeasure.toMeasure_map]
    change
      Measure.map profileOfUnitInterval
          (volume : Measure (Set.Icc (0 : ℝ) 1)) {profile} =
        0
    rw [Measure.map_apply profileOfUnitInterval_measurable
      (measurableSet_singleton profile)]
    exact
      Set.Subsingleton.measure_zero
        (by
          intro first hfirst second hsecond
          apply profileOfUnitInterval_injective
          exact hfirst.trans hsecond.symm)
        (volume : Measure (Set.Icc (0 : ℝ) 1))

/-- The arbitrary-measure profile law is not the measure associated with any
countably supported PMF. -/
theorem no_pmf_representation :
    ¬ ∃ law : PMF game.PureProfile,
      @PMF.toMeasure game.PureProfile profileMeasurableSpace law =
        profileMeasure := by
  rintro ⟨law, hlaw⟩
  have hsupportOne :
      @PMF.toMeasure game.PureProfile profileMeasurableSpace law
          law.support =
        1 :=
    (law.toMeasure_apply_eq_one_iff
      law.support_countable.measurableSet).mpr Set.Subset.rfl
  have hsupportZero :
      profileMeasure law.support = 0 :=
    law.support_countable.measure_zero _
  rw [hlaw, hsupportZero] at hsupportOne
  exact zero_ne_one hsupportOne

end Examples.ArbitraryMeasurePureStrategyBoundary
