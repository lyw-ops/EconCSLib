/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.General
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Arbitrary-measure pure-strategy laws

This module defines probability measures on explicitly measurable pure
strategy and pure-profile carriers. It does not infer a measurable structure
on dependent function spaces.

`ArbitraryMeasurePureProfileLaw` is a joint law on complete pure profiles and
may correlate players. It is different from `MixedProfile`, whose finite-player
FiniteLaw semantics samples player plans independently, and from
`DiscreteGeneralProfile`, whose carrier is a playerwise FiniteLaw over behavioral
strategies.

The primitive semantics is measurable pushforward through a caller-certified
profile evaluator. Pure and FiniteLaw laws embed exactly, and FiniteLaw pushforward agrees
as a complete measure. No unrestricted arbitrary-measure Kuhn equivalence is
claimed: measurable evaluation, recall, standard-Borel disintegration,
independence, and null-information conditioning remain explicit downstream
obligations. See `docs/design/efg-arbitrary-measure-strategies.md`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

local macro "finiteLawMeasure(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0)

private theorem finiteLawMeasure_isProbability
    {X : Type*} [MeasurableSpace X] (law : FiniteLaw X) :
    IsProbabilityMeasure finiteLawMeasure(law) := by
  constructor
  change finiteLawMeasure(law) Set.univ = 1
  have hzero : ((0 : ℚ≥0) : ENNReal) = 0 := by
    change (((0 : ℚ≥0) : NNReal) : ENNReal) = 0
    simp
  have hadd (p q : ℚ≥0) :
      ((p + q : ℚ≥0) : ENNReal) =
        (p : ENNReal) + (q : ENNReal) := by
    change (((p + q : ℚ≥0) : NNReal) : ENNReal) =
      ((p : NNReal) : ENNReal) + ((q : NNReal) : ENNReal)
    simp
  have hsum :
      finiteLawMeasure(law) Set.univ =
        ((FiniteLaw.totalWeight law.atoms : ℚ≥0) : ENNReal) := by
    induction law.atoms with
    | nil => simp [FiniteLaw.totalWeight, hzero]
    | cons atom atoms ih =>
        simp [FiniteLaw.totalWeight, ih, hadd]
  rw [hsum, FiniteLaw.totalWeight_atoms]
  change (((1 : ℚ≥0) : NNReal) : ENNReal) = 1
  norm_num

private theorem finiteLawMeasure_map
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : FiniteLaw X) (f : X → Y) (hf : Measurable f) :
    (finiteLawMeasure(law)).map f =
      finiteLawMeasure(law.map f) := by
  rw [FiniteLaw.map_atoms]
  ext event hevent
  rw [Measure.map_apply hf hevent]
  induction law.atoms with
  | nil => simp
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, weight⟩
      simp only [List.map_cons, List.foldr_cons]
      simp [Measure.dirac_apply' _ hevent,
        Measure.dirac_apply' _ (hf hevent), ih]
      rfl

namespace ExtensiveGame.ObservedGame

universe uN uU uOutcome

variable {N : Type uN} {U : Type uU}

/-- Explicit measurable structures for dependent pure strategies and complete
pure profiles.

The coordinate condition is the minimum bridge needed to recover player
marginals from a joint profile law. It does not assert that the profile space
is a product measurable space or that arbitrary player laws admit an
independent product. -/
structure PureProfileMeasurableModel (G : ObservedGame N U) where
  /-- Measurable space on each player's complete pure-strategy carrier. -/
  strategyMeasurableSpace :
    (i : N) → MeasurableSpace (G.PureStrategy i)
  /-- Measurable space on complete pure profiles. -/
  profileMeasurableSpace : MeasurableSpace G.PureProfile
  /-- Every player-coordinate projection is measurable. -/
  coordinate_measurable :
    ∀ i : N,
      @Measurable G.PureProfile (G.PureStrategy i)
        profileMeasurableSpace (strategyMeasurableSpace i)
        (fun profile => profile i)

variable {G : ObservedGame N U}

/-- An arbitrary probability measure on one explicitly measurable pure
strategy carrier. -/
abbrev ArbitraryMeasurePureStrategy
    (model : G.PureProfileMeasurableModel) (i : N) :=
  @ProbabilityMeasure (G.PureStrategy i)
    (model.strategyMeasurableSpace i)

/-- A joint, potentially correlated arbitrary probability measure on complete
pure profiles. -/
abbrev ArbitraryMeasurePureProfileLaw
    (model : G.PureProfileMeasurableModel) :=
  @ProbabilityMeasure G.PureProfile model.profileMeasurableSpace

namespace ArbitraryMeasurePureProfileLaw

variable (model : G.PureProfileMeasurableModel)

/-- Embed one complete pure profile as a Dirac probability law. -/
noncomputable def ofPure (profile : G.PureProfile) :
    G.ArbitraryMeasurePureProfileLaw model := by
  letI : MeasurableSpace G.PureProfile :=
    model.profileMeasurableSpace
  exact
    ⟨Measure.dirac profile,
      Measure.dirac.isProbabilityMeasure⟩

/-- Embed a finite exact law on complete pure profiles as its Mathlib
probability measure. -/
noncomputable def ofFiniteLaw (law : FiniteLaw G.PureProfile) :
    G.ArbitraryMeasurePureProfileLaw model := by
  letI : MeasurableSpace G.PureProfile :=
    model.profileMeasurableSpace
  exact ⟨finiteLawMeasure(law), finiteLawMeasure_isProbability law⟩

/-- Push a joint pure-profile law through an explicitly measurable evaluator.
-/
noncomputable def outcomeLaw
    (law : G.ArbitraryMeasurePureProfileLaw model)
    {Outcome : Type uOutcome} [MeasurableSpace Outcome]
    (evaluate : G.PureProfile → Outcome)
    (hevaluate :
      @Measurable G.PureProfile Outcome
        model.profileMeasurableSpace inferInstance evaluate) :
    ProbabilityMeasure Outcome := by
  letI : MeasurableSpace G.PureProfile :=
    model.profileMeasurableSpace
  exact ProbabilityMeasure.map law hevaluate.aemeasurable

/-- Complete-path law generated by a measurable pure-profile executor.

The executor is supplied explicitly because measurability of EFG execution
does not follow from the carrier alone. -/
noncomputable def pathLaw
    (law : G.ArbitraryMeasurePureProfileLaw model)
    [MeasurableSpace G.base.CompletePlay]
    (execute : G.PureProfile → G.base.CompletePlay)
    (hexecute :
      @Measurable G.PureProfile G.base.CompletePlay
        model.profileMeasurableSpace inferInstance execute) :
    ProbabilityMeasure G.base.CompletePlay := by
  letI : MeasurableSpace G.PureProfile :=
    model.profileMeasurableSpace
  exact law.outcomeLaw model execute hexecute

/-- The underlying measure of a finite-law embedding is its weighted Dirac
fold. -/
@[simp]
theorem toMeasure_ofFiniteLaw (law : FiniteLaw G.PureProfile) :
    @ProbabilityMeasure.toMeasure G.PureProfile
        model.profileMeasurableSpace (ofFiniteLaw model law) =
      law.atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) •
            @Measure.dirac _ model.profileMeasurableSpace atom.1 + rest)
        0 :=
  rfl

/-- Measurable semantics of a FiniteLaw embedding agrees with the existing FiniteLaw
pushforward as a complete outcome measure. -/
theorem outcomeLaw_ofFiniteLaw
    (law : FiniteLaw G.PureProfile)
    {Outcome : Type uOutcome} [MeasurableSpace Outcome]
    (evaluate : G.PureProfile → Outcome)
    (hevaluate :
      @Measurable G.PureProfile Outcome
        model.profileMeasurableSpace inferInstance evaluate) :
    ((outcomeLaw model (ofFiniteLaw model law) evaluate hevaluate :
        ProbabilityMeasure Outcome) : Measure Outcome) =
      finiteLawMeasure(law.map evaluate) := by
  letI : MeasurableSpace G.PureProfile :=
    model.profileMeasurableSpace
  exact finiteLawMeasure_map law evaluate hevaluate

/-- A pure profile embedded through the FiniteLaw route agrees with the direct
Dirac embedding. -/
theorem ofFiniteLaw_pure (profile : G.PureProfile) :
    ofFiniteLaw model (FiniteLaw.pure profile) =
      ofPure model profile := by
  letI : MeasurableSpace G.PureProfile :=
    model.profileMeasurableSpace
  apply ProbabilityMeasure.toMeasure_injective
  change finiteLawMeasure(FiniteLaw.pure profile) = Measure.dirac profile
  rw [FiniteLaw.pure_atoms]
  simp only [List.foldr_cons, List.foldr_nil, add_zero]
  change
    (((1 : ℚ≥0) : NNReal) : ENNReal) • Measure.dirac profile =
      Measure.dirac profile
  simp

/-- The marginal law of one player is the measurable pushforward of the joint
profile law through that coordinate. -/
noncomputable def marginal
    (law : G.ArbitraryMeasurePureProfileLaw model)
    (i : N) :
    G.ArbitraryMeasurePureStrategy model i := by
  letI : MeasurableSpace G.PureProfile :=
    model.profileMeasurableSpace
  letI : MeasurableSpace (G.PureStrategy i) :=
    model.strategyMeasurableSpace i
  exact
    ProbabilityMeasure.map law
      (model.coordinate_measurable i).aemeasurable

end ArbitraryMeasurePureProfileLaw

namespace MixedProfile

/-- Embed the existing finite-player independent mixed profile into the
arbitrary-measure joint carrier.

Independence is established first by `pureProfileLaw`; `ofFiniteLaw` then changes
only the law representation. -/
noncomputable def toArbitraryMeasurePureProfileLaw
    [Fintype N] [LinearOrder N]
    (model : G.PureProfileMeasurableModel)
    (profile : G.MixedProfile) :
    G.ArbitraryMeasurePureProfileLaw model :=
  ArbitraryMeasurePureProfileLaw.ofFiniteLaw model
    (profile.pureProfileLaw G)

/-- The arbitrary-measure embedding of an existing mixed profile has exactly
the weighted-Dirac measure of its finite joint law. -/
theorem toMeasure_toArbitraryMeasurePureProfileLaw
    [Fintype N] [LinearOrder N]
    (model : G.PureProfileMeasurableModel)
    (profile : G.MixedProfile) :
    @ProbabilityMeasure.toMeasure G.PureProfile
        model.profileMeasurableSpace
        (profile.toArbitraryMeasurePureProfileLaw model) =
      (profile.pureProfileLaw G).atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) •
            @Measure.dirac _ model.profileMeasurableSpace atom.1 + rest)
        0 :=
  rfl

end MixedProfile

end ExtensiveGame.ObservedGame
