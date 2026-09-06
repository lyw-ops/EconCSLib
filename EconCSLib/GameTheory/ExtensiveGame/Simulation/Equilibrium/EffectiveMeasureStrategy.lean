/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.MeasureStrategy
import EconCSLib.Math.Probability.Effective.Semantics

/-!
# Effective queries for arbitrary-measure pure-profile laws

This module connects executable coded-event queries to the existing analytic
pure-profile semantics.  A caller supplies an `EffectiveLaw` representing the
joint profile measure and an executable preimage compiler for the requested
map.  The resulting effective laws then represent the exact analytic
`marginal`, `outcomeLaw`, and `pathLaw` pushforwards.

The bridge does not claim that arbitrary measurable sets can be compiled.  It
applies only to the selected event languages and preimage compilers supplied
in its hypotheses, while preserving the general probability-measure API as
the semantic target.
-/

open MeasureTheory

namespace ExtensiveGame.ObservedGame

universe uN uU uProfileCode uTargetCode uOutcome

variable {N : Type uN} {U : Type uU}
variable {G : ObservedGame N U}

namespace ArbitraryMeasurePureProfileLaw

variable (model : G.PureProfileMeasurableModel)

/-- An effective coordinate pushforward represents the analytic player
marginal when its event compiler denotes coordinate preimages. -/
theorem effective_marginal_represents
    {ProfileCode : Type uProfileCode} {StrategyCode : Type uTargetCode}
    (profileLaw : G.ArbitraryMeasurePureProfileLaw model)
    (i : N)
    (law : EffectiveProbability.EffectiveLaw ProfileCode)
    (coordinate :
      EffectiveProbability.EffectiveMap ProfileCode StrategyCode)
    (profileSemantics :
      @EffectiveProbability.EventSemantics ProfileCode G.PureProfile
        model.profileMeasurableSpace)
    (strategySemantics :
      @EffectiveProbability.EventSemantics StrategyCode (G.PureStrategy i)
        (model.strategyMeasurableSpace i))
    (hlaw :
      @EffectiveProbability.EffectiveLaw.Represents
        ProfileCode G.PureProfile model.profileMeasurableSpace
        law profileSemantics
        (@ProbabilityMeasure.toMeasure G.PureProfile
          model.profileMeasurableSpace profileLaw))
    (hcoordinate :
      @EffectiveProbability.EffectiveMap.Represents
        ProfileCode StrategyCode G.PureProfile (G.PureStrategy i)
        model.profileMeasurableSpace (model.strategyMeasurableSpace i)
        coordinate profileSemantics strategySemantics
        (fun profile => profile i)) :
    @EffectiveProbability.EffectiveLaw.Represents
      StrategyCode (G.PureStrategy i) (model.strategyMeasurableSpace i)
      (law.map coordinate) strategySemantics
      (@ProbabilityMeasure.toMeasure (G.PureStrategy i)
        (model.strategyMeasurableSpace i)
        (marginal model profileLaw i)) := by
  letI : MeasurableSpace G.PureProfile := model.profileMeasurableSpace
  letI : MeasurableSpace (G.PureStrategy i) :=
    model.strategyMeasurableSpace i
  simpa [marginal] using hlaw.map hcoordinate

/-- An effective evaluator pushforward represents the analytic outcome law
when its compiler certifies measurability and denotes evaluator preimages. -/
theorem effective_outcomeLaw_represents
    {ProfileCode : Type uProfileCode} {OutcomeCode : Type uTargetCode}
    (profileLaw : G.ArbitraryMeasurePureProfileLaw model)
    {Outcome : Type uOutcome} [MeasurableSpace Outcome]
    (evaluate : G.PureProfile → Outcome)
    (law : EffectiveProbability.EffectiveLaw ProfileCode)
    (evaluator :
      EffectiveProbability.EffectiveMap ProfileCode OutcomeCode)
    (profileSemantics :
      @EffectiveProbability.EventSemantics ProfileCode G.PureProfile
        model.profileMeasurableSpace)
    (outcomeSemantics :
      EffectiveProbability.EventSemantics OutcomeCode Outcome)
    (hlaw :
      @EffectiveProbability.EffectiveLaw.Represents
        ProfileCode G.PureProfile model.profileMeasurableSpace
        law profileSemantics
        (@ProbabilityMeasure.toMeasure G.PureProfile
          model.profileMeasurableSpace profileLaw))
    (hevaluator :
      @EffectiveProbability.EffectiveMap.Represents
        ProfileCode OutcomeCode G.PureProfile Outcome
        model.profileMeasurableSpace inferInstance
        evaluator profileSemantics outcomeSemantics evaluate) :
    (law.map evaluator).Represents outcomeSemantics
      (outcomeLaw model profileLaw evaluate (by
        letI : MeasurableSpace G.PureProfile :=
          model.profileMeasurableSpace
        exact hevaluator.measurable) : Measure Outcome) := by
  letI : MeasurableSpace G.PureProfile := model.profileMeasurableSpace
  simpa [outcomeLaw] using hlaw.map hevaluator

/-- An effective complete-play executor represents the analytic path law when
its compiler certifies measurability and denotes executor preimages. -/
theorem effective_pathLaw_represents
    {ProfileCode : Type uProfileCode} {PathCode : Type uTargetCode}
    (profileLaw : G.ArbitraryMeasurePureProfileLaw model)
    [MeasurableSpace G.base.CompletePlay]
    (execute : G.PureProfile → G.base.CompletePlay)
    (law : EffectiveProbability.EffectiveLaw ProfileCode)
    (executor :
      EffectiveProbability.EffectiveMap ProfileCode PathCode)
    (profileSemantics :
      @EffectiveProbability.EventSemantics ProfileCode G.PureProfile
        model.profileMeasurableSpace)
    (pathSemantics :
      EffectiveProbability.EventSemantics PathCode G.base.CompletePlay)
    (hlaw :
      @EffectiveProbability.EffectiveLaw.Represents
        ProfileCode G.PureProfile model.profileMeasurableSpace
        law profileSemantics
        (@ProbabilityMeasure.toMeasure G.PureProfile
          model.profileMeasurableSpace profileLaw))
    (hexecutor :
      @EffectiveProbability.EffectiveMap.Represents
        ProfileCode PathCode G.PureProfile G.base.CompletePlay
        model.profileMeasurableSpace inferInstance
        executor profileSemantics pathSemantics execute) :
    (law.map executor).Represents pathSemantics
      (pathLaw model profileLaw execute (by
        letI : MeasurableSpace G.PureProfile :=
          model.profileMeasurableSpace
        exact hexecutor.measurable) :
        Measure G.base.CompletePlay) := by
  letI : MeasurableSpace G.PureProfile := model.profileMeasurableSpace
  simpa [pathLaw, outcomeLaw] using hlaw.map hexecutor

end ArbitraryMeasurePureProfileLaw

end ExtensiveGame.ObservedGame
