/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior

/-!
# Infinite execution for observed behavioral games

This adapter specializes the generic infinite history-path law to behavioral
profiles and the declared chance kernels of an observed chance game. It keeps
the finite-marginal theorem available at the representation-facing API.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.ObservedChanceGame.BehavioralProfile

variable {N U : Type*} (G : ObservedChanceGame N U)

/-- Terminal-absorbing one-step history kernel induced by a behavioral profile
and the observed game's declared chance laws. -/
noncomputable def stepKernel
    [(s : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal s)]
    [MeasurableSpace
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [MeasurableSingletonClass
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [Countable
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    (profile : G.observed.BehavioralProfile) :
    Kernel
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)
      (G.observed.base.toArena.HistoryFrom G.observed.base.init) :=
  Arena.stepKernel (toHistoryPolicy G profile)

instance stepKernel_isMarkov
    [(s : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal s)]
    [MeasurableSpace
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [MeasurableSingletonClass
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [Countable
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    (profile : G.observed.BehavioralProfile) :
    IsMarkovKernel (stepKernel G profile) := by
  rw [stepKernel]
  infer_instance

/-- Infinite terminal-absorbing history-path law induced by a behavioral
profile and the observed game's chance kernels. -/
noncomputable def pathLaw
    [(s : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal s)]
    [MeasurableSpace
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [MeasurableSingletonClass
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [Countable
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    Measure
      (ℕ →
        G.observed.base.toArena.HistoryFrom G.observed.base.init) :=
  Arena.pathLaw (toHistoryPolicy G profile) current

instance pathLaw_isProbability
    [(s : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal s)]
    [MeasurableSpace
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [MeasurableSingletonClass
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [Countable
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    IsProbabilityMeasure (pathLaw G profile current) := by
  rw [pathLaw]
  infer_instance

/-- The behavioral path law starts at the supplied complete history. -/
theorem pathLaw_initial
    [(s : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal s)]
    [MeasurableSpace
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [MeasurableSingletonClass
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [Countable
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    (pathLaw G profile current).map (fun path => path 0) =
      Measure.dirac current :=
  Arena.pathLaw_initial (toHistoryPolicy G profile) current

/-- At every event time, the behavioral infinite-path marginal is exactly
the existing bounded behavioral PMF executor, converted to a measure. -/
theorem pathLaw_finiteMarginal_eq_stochasticHistoryPMFFrom_toMeasure
    [(s : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal s)]
    [MeasurableSpace
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [MeasurableSingletonClass
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [Countable
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (n : ℕ) :
    (pathLaw G profile current).map (fun path => path n) =
      (G.observed.base.toArena.stochasticHistoryPMFFrom
        (toHistoryPolicy G profile) current n).toMeasure :=
  Arena.pathLaw_finiteMarginal_eq_stochasticHistoryPMFFrom_toMeasure
    (toHistoryPolicy G profile) current n

/-- Behavioral almost-sure termination is the generic path-law termination
predicate specialized through `toHistoryPolicy`. -/
abbrev AETerminates
    [(s : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal s)]
    [MeasurableSpace
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [MeasurableSingletonClass
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [Countable
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) : Prop :=
  Arena.AETerminates (toHistoryPolicy G profile) current

end ExtensiveGame.ObservedChanceGame.BehavioralProfile
