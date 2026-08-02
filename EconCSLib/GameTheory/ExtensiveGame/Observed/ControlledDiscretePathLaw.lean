/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledDiscreteLaw
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledLaw

/-!
# Discrete implementation of controlled complete-path probability semantics

This module connects PMF-valued behavioral strategies and chance kernels to
the representation-independent `ControlledObservedGame.CompletePathLawSemantics`.
Countability and discrete chance assumptions occur only in this constructor,
not in the maximum interface.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.DiscreteControlledObservedChanceGame

variable {N : Type*}
  (G : DiscreteControlledObservedChanceGame N)

/-- Complete discrete history-path law for one behavioral profile. -/
noncomputable def behavioralPathLaw
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [MeasurableSpace G.observed.base.History]
    [MeasurableSingletonClass G.observed.base.History]
    [Countable G.observed.base.History]
    (profile : G.BehavioralProfile)
    (current : G.observed.base.History) :
    Measure (ℕ → G.observed.base.History) :=
  Arena.pathLaw
    (BehavioralProfile.toHistoryPolicy G profile) current

/-- The actual discrete behavioral executor instantiates the maximum lawful
complete-path probability interface. -/
noncomputable def behavioralCompletePathLawSemantics
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [MeasurableSpace G.observed.base.History]
    [MeasurableSingletonClass G.observed.base.History]
    [Countable G.observed.base.History] :
    G.observed.CompletePathLawSemantics where
  Strategy := G.BehavioralStrategy
  pathLaw := fun profile current =>
    G.behavioralPathLaw profile current
  pathLaw_isProbability := by
    intro profile current
    change IsProbabilityMeasure
      (Arena.pathLaw
        (BehavioralProfile.toHistoryPolicy G profile) current)
    infer_instance
  pathLaw_ae_legal := by
    intro profile current
    exact Arena.pathLaw_ae_isCompletePlayPathFrom
      (BehavioralProfile.toHistoryPolicy G profile) current

/-- The discrete semantic carrier realizes the established Ionescu--Tulcea
history-path executor definitionally. -/
theorem behavioralCompletePathLawSemantics_realizesExecution
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [MeasurableSpace G.observed.base.History]
    [MeasurableSingletonClass G.observed.base.History]
    [Countable G.observed.base.History] :
    (G.behavioralCompletePathLawSemantics).RealizesExecution
      G.behavioralPathLaw := by
  intro _profile _current
  rfl

end ExtensiveGame.DiscreteControlledObservedChanceGame
