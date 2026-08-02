/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledDiscreteLawCompat
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledDiscretePathLaw
import EconCSLib.GameTheory.ExtensiveGame.Observed.InfiniteExecution

/-!
# Payoff-aware adapters for complete path-law equivalence

The unique maximum carrier is
`ControlledObservedGame.CompletePathLawSemantics`.  This module preserves the
established `ObservedChanceGame` spelling by projection; it does not define a
second strategy/law structure and no longer stores informal
`StrategicMode`/`ChanceSemantics` tags.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.ObservedChanceGame

universe uN uU uStrategy uOutcome

variable {N : Type uN} {U : Type uU}

/-- Compatibility spelling for the payoff-free lawful probability semantics. -/
abbrev CompletePathLawSemantics
    (G : ObservedChanceGame N U)
    [historyMeasurable :
      MeasurableSpace G.observed.base.History] :=
  @ControlledObservedGame.CompletePathLawSemantics.{uN, uStrategy}
    N G.observed.toControlledObservedGame historyMeasurable

namespace CompletePathLawSemantics

variable {G : ObservedChanceGame N U}
  [historyMeasurable :
    MeasurableSpace G.observed.base.History]

local instance controlledHistoryMeasurable :
    MeasurableSpace
      G.observed.toControlledObservedGame.base.History :=
  historyMeasurable

/-- Complete profiles for one path-law semantics. -/
abbrev Profile (S : G.CompletePathLawSemantics) :=
  (i : N) → S.Strategy i

/-- Compatibility spelling for same-game complete-path law equality. -/
def CompletePathLawEquivalentAt
    (S T : G.CompletePathLawSemantics)
    (source : S.Profile) (target : T.Profile)
    (current : G.observed.base.History) : Prop :=
  S.pathLaw source current = T.pathLaw target current

/-- Equality of the probabilities assigned to one path event. -/
def PathEventLawEquivalentAt
    (S T : G.CompletePathLawSemantics)
    (event : Set (ℕ → G.observed.base.History))
    (source : S.Profile) (target : T.Profile)
    (current : G.observed.base.History) : Prop :=
  S.pathLaw source current event =
    T.pathLaw target current event

/-- Equality after an explicitly measurable complete-path observation. -/
def PathOutcomeLawEquivalentAt
    (S T : G.CompletePathLawSemantics)
    [MeasurableSpace Outcome]
    (observer : (ℕ → G.observed.base.History) → Outcome)
    (_hobserver : Measurable observer)
    (source : S.Profile) (target : T.Profile)
    (current : G.observed.base.History) : Prop :=
  (S.pathLaw source current).map observer =
    (T.pathLaw target current).map observer

/-- Equality on every externally selected continuation root. -/
def CompletePathLawEquivalentOnRoots
    (S T : G.CompletePathLawSemantics)
    (roots : G.observed.RootPresentation)
    (source : S.Profile) (target : T.Profile) : Prop :=
  ∀ current, roots.IsRoot current →
    S.CompletePathLawEquivalentAt T source target current

/-- Equality at every legal continuation history. -/
def CompletePathLawEquivalentOnAllContinuations
    (S T : G.CompletePathLawSemantics)
    (source : S.Profile) (target : T.Profile) : Prop :=
  S.CompletePathLawEquivalentOnRoots T
    (ObservedGame.ContinuationRootPresentation.allHistories
      G.observed.base)
    source target

/-- Equality at the initial history only. -/
def CompletePathLawEquivalentInitially
    (S T : G.CompletePathLawSemantics)
    (source : S.Profile) (target : T.Profile) : Prop :=
  S.CompletePathLawEquivalentOnRoots T
    (ObservedGame.ContinuationRootPresentation.initialOnly
      G.observed.base)
    source target

/-- Complete path-law equality implies event-probability equality. -/
theorem CompletePathLawEquivalentAt.event
    {S T : G.CompletePathLawSemantics}
    {source : S.Profile} {target : T.Profile}
    {current : G.observed.base.History}
    (h : S.CompletePathLawEquivalentAt T source target current)
    (event : Set (ℕ → G.observed.base.History)) :
    S.PathEventLawEquivalentAt T event source target current := by
  unfold PathEventLawEquivalentAt
  rw [h]

/-- Complete path-law equality implies every measurable pushforward equality. -/
theorem CompletePathLawEquivalentAt.mappedOutcome
    {S T : G.CompletePathLawSemantics}
    [MeasurableSpace Outcome]
    {source : S.Profile} {target : T.Profile}
    {current : G.observed.base.History}
    (h : S.CompletePathLawEquivalentAt T source target current)
    (observer : (ℕ → G.observed.base.History) → Outcome)
    (hobserver : Measurable observer) :
    S.PathOutcomeLawEquivalentAt
      T observer hobserver source target current := by
  unfold PathOutcomeLawEquivalentAt
  rw [h]

/-- Compatibility spelling for the canonical same-game realization. -/
abbrev CompletePathLawRealization
    (S T : G.CompletePathLawSemantics) :=
  ControlledObservedGame.CompletePathLawSemantics.CompletePathLawRealization
    S T

namespace CompletePathLawRealization

variable {S T : G.CompletePathLawSemantics}

/-- Map a complete source profile componentwise. -/
abbrev mapProfile
    (R : S.CompletePathLawRealization T) :=
  ControlledObservedGame.CompletePathLawSemantics.CompletePathLawRealization.mapProfile
    R

/-- Componentwise realization commutes with unilateral replacement. -/
theorem mapProfile_update
    [DecidableEq N]
    (R : S.CompletePathLawRealization T)
    (profile : S.Profile) (i : N)
    (deviation : S.Strategy i) :
    R.mapProfile (Function.update profile i deviation) =
      Function.update (R.mapProfile profile) i
        (R.mapStrategy i deviation) :=
  ControlledObservedGame.CompletePathLawSemantics.CompletePathLawRealization.mapProfile_update
    R profile i deviation

/-- Exact law preservation for every mapped unilateral deviation. -/
theorem unilateralPathLaw_eq
    [DecidableEq N]
    (R : S.CompletePathLawRealization T)
    (profile : S.Profile) (i : N)
    (deviation : S.Strategy i)
    (current : G.observed.base.History) :
    S.pathLaw
        (Function.update profile i deviation) current =
      T.pathLaw
        (Function.update (R.mapProfile profile) i
          (R.mapStrategy i deviation))
        current := by
  rw [← R.mapProfile_update profile i deviation]
  exact R.pathLaw_eq
    (Function.update profile i deviation) current

end CompletePathLawRealization

end CompletePathLawSemantics

/-- The established discrete behavioral executor, projected into the unique
payoff-free lawful probability carrier. -/
noncomputable def behavioralCompletePathLawSemantics
    (G : ObservedChanceGame N U)
    [terminalDecidable :
      (state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [historyMeasurable :
      MeasurableSpace G.observed.base.History]
    [historySingleton :
      MeasurableSingletonClass G.observed.base.History]
    [historyCountable :
      Countable G.observed.base.History] :
    G.CompletePathLawSemantics :=
  @DiscreteControlledObservedChanceGame.behavioralCompletePathLawSemantics
    N G.toDiscreteControlledObservedChanceGame
    terminalDecidable historyMeasurable historySingleton historyCountable

end ExtensiveGame.ObservedChanceGame
