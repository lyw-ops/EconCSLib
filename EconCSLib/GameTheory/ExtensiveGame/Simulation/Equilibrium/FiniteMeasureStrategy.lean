/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.FiniteMeasureStrategy
import EconCSLib.GameTheory.ExtensiveGame.Observed.MeasureStrategy
import EconCSLib.Math.Probability.FiniteLaw.Measure

/-!
# Analytic semantics of finite pure-profile laws

The executable `ObservedGame.FinitePureProfileLaw` layer computes marginals,
outcomes, and complete paths with `FiniteLaw.map` and imports no measure
theory.  This analytic leaf proves that those three algorithms agree exactly
with the corresponding `ArbitraryMeasurePureProfileLaw` operations after the
finite joint law is embedded as a weighted sum of Dirac measures.

## Main results

* `FinitePureProfileLaw.toMeasure_analyticMarginal`;
* `FinitePureProfileLaw.toMeasure_analyticOutcomeLaw`;
* `FinitePureProfileLaw.toMeasure_analyticPathLaw`.

The corresponding `analytic..._eq_iff` theorems lift each statement from
underlying measures to equality of `ProbabilityMeasure`s without introducing
a second measure-producing definition.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.ObservedGame.FinitePureProfileLaw

universe uN uU uOutcome

variable {N : Type uN} {U : Type uU}
variable {G : ObservedGame N U}

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest)
    0 atoms

/-- The analytic marginal of an embedded finite joint law is exactly the
weighted-Dirac interpretation of the executable finite marginal. -/
theorem toMeasure_analyticMarginal
    (model : G.PureProfileMeasurableModel)
    (law : G.FinitePureProfileLaw) (i : N) :
    @ProbabilityMeasure.toMeasure (G.PureStrategy i)
        (model.strategyMeasurableSpace i)
        (ArbitraryMeasurePureProfileLaw.marginal model
          (ArbitraryMeasurePureProfileLaw.ofFiniteLaw model law) i) =
      (law.marginal i).atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) •
            @Measure.dirac _ (model.strategyMeasurableSpace i) atom.1 + rest)
        0 := by
  letI : MeasurableSpace G.PureProfile :=
    model.profileMeasurableSpace
  letI : MeasurableSpace (G.PureStrategy i) :=
    model.strategyMeasurableSpace i
  change
    ((ArbitraryMeasurePureProfileLaw.outcomeLaw model
        (ArbitraryMeasurePureProfileLaw.ofFiniteLaw model law)
        (fun profile => profile i) (model.coordinate_measurable i) :
      ProbabilityMeasure (G.PureStrategy i)) :
      Measure (G.PureStrategy i)) =
      μ[(law.marginal i).atoms]
  exact
    ArbitraryMeasurePureProfileLaw.outcomeLaw_ofFiniteLaw model law
      (fun profile => profile i) (model.coordinate_measurable i)

/-- A candidate analytic marginal is the original marginal exactly when its
underlying measure is the executable marginal's finite Dirac interpretation.
-/
theorem analyticMarginal_eq_iff
    (model : G.PureProfileMeasurableModel)
    (law : G.FinitePureProfileLaw) (i : N)
    (candidate : G.ArbitraryMeasurePureStrategy model i) :
    ArbitraryMeasurePureProfileLaw.marginal model
        (ArbitraryMeasurePureProfileLaw.ofFiniteLaw model law) i = candidate ↔
      @ProbabilityMeasure.toMeasure (G.PureStrategy i)
          (model.strategyMeasurableSpace i) candidate =
        (law.marginal i).atoms.foldr
          (fun atom rest =>
            (atom.2 : ENNReal) •
              @Measure.dirac _ (model.strategyMeasurableSpace i) atom.1 + rest)
          0 := by
  constructor
  · intro heq
    rw [← heq]
    exact toMeasure_analyticMarginal model law i
  · intro hmeasure
    letI : MeasurableSpace (G.PureStrategy i) :=
      model.strategyMeasurableSpace i
    apply ProbabilityMeasure.toMeasure_injective
    exact (toMeasure_analyticMarginal model law i).trans hmeasure.symm

/-- Analytic measurable pushforward and executable finite pushforward agree as
complete outcome measures. -/
theorem toMeasure_analyticOutcomeLaw
    (model : G.PureProfileMeasurableModel)
    (law : G.FinitePureProfileLaw)
    {Outcome : Type uOutcome} [MeasurableSpace Outcome]
    (evaluate : G.PureProfile → Outcome)
    (hevaluate :
      @Measurable G.PureProfile Outcome
        model.profileMeasurableSpace inferInstance evaluate) :
    ((ArbitraryMeasurePureProfileLaw.outcomeLaw model
        (ArbitraryMeasurePureProfileLaw.ofFiniteLaw model law)
        evaluate hevaluate : ProbabilityMeasure Outcome) : Measure Outcome) =
      μ[(law.outcomeLaw evaluate).atoms] :=
  ArbitraryMeasurePureProfileLaw.outcomeLaw_ofFiniteLaw model law
    evaluate hevaluate

/-- A candidate analytic outcome law is the original pushforward exactly when
its underlying measure is the executable outcome law's finite Dirac
interpretation. -/
theorem analyticOutcomeLaw_eq_iff
    (model : G.PureProfileMeasurableModel)
    (law : G.FinitePureProfileLaw)
    {Outcome : Type uOutcome} [MeasurableSpace Outcome]
    (evaluate : G.PureProfile → Outcome)
    (hevaluate :
      @Measurable G.PureProfile Outcome
        model.profileMeasurableSpace inferInstance evaluate)
    (candidate : ProbabilityMeasure Outcome) :
    ArbitraryMeasurePureProfileLaw.outcomeLaw model
        (ArbitraryMeasurePureProfileLaw.ofFiniteLaw model law)
        evaluate hevaluate = candidate ↔
      (candidate : Measure Outcome) =
        μ[(law.outcomeLaw evaluate).atoms] := by
  constructor
  · intro heq
    rw [← heq]
    exact toMeasure_analyticOutcomeLaw model law evaluate hevaluate
  · intro hmeasure
    apply ProbabilityMeasure.toMeasure_injective
    exact
      (toMeasure_analyticOutcomeLaw model law evaluate hevaluate).trans
        hmeasure.symm

/-- Analytic complete-path pushforward and executable finite path pushforward
agree as complete measures. -/
theorem toMeasure_analyticPathLaw
    (model : G.PureProfileMeasurableModel)
    (law : G.FinitePureProfileLaw)
    [MeasurableSpace G.base.CompletePlay]
    (execute : G.PureProfile → G.base.CompletePlay)
    (hexecute :
      @Measurable G.PureProfile G.base.CompletePlay
        model.profileMeasurableSpace inferInstance execute) :
    ((ArbitraryMeasurePureProfileLaw.pathLaw model
        (ArbitraryMeasurePureProfileLaw.ofFiniteLaw model law)
        execute hexecute : ProbabilityMeasure G.base.CompletePlay) :
      Measure G.base.CompletePlay) =
      μ[(law.pathLaw execute).atoms] :=
  ArbitraryMeasurePureProfileLaw.outcomeLaw_ofFiniteLaw model law
    execute hexecute

/-- A candidate analytic path law is the original path pushforward exactly
when its underlying measure is the executable path law's finite Dirac
interpretation. -/
theorem analyticPathLaw_eq_iff
    (model : G.PureProfileMeasurableModel)
    (law : G.FinitePureProfileLaw)
    [MeasurableSpace G.base.CompletePlay]
    (execute : G.PureProfile → G.base.CompletePlay)
    (hexecute :
      @Measurable G.PureProfile G.base.CompletePlay
        model.profileMeasurableSpace inferInstance execute)
    (candidate : ProbabilityMeasure G.base.CompletePlay) :
    ArbitraryMeasurePureProfileLaw.pathLaw model
        (ArbitraryMeasurePureProfileLaw.ofFiniteLaw model law)
        execute hexecute = candidate ↔
      (candidate : Measure G.base.CompletePlay) =
        μ[(law.pathLaw execute).atoms] := by
  constructor
  · intro heq
    rw [← heq]
    exact toMeasure_analyticPathLaw model law execute hexecute
  · intro hmeasure
    apply ProbabilityMeasure.toMeasure_injective
    exact
      (toMeasure_analyticPathLaw model law execute hexecute).trans
        hmeasure.symm

end ExtensiveGame.ObservedGame.FinitePureProfileLaw
