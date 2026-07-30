/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Conditioning
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Observed

/-!
# Continuation.ObservedConditioning — observed conditional compatibility

This module lifts the raw positive-prefix conditional compatibility theorem
to canonical observed-game histories.

For a profile started from `initialHistory`, it defines:

* the marginal mass of another complete history's canonical event prefix;
* the regular conditional shifted event-path law at that prefix;
* its state-path projection;
* bounded expected utility under that conditional state law.

When the canonical prefix has nonzero marginal mass, these laws and expected
utilities agree exactly with constructive absolute-prefix continuation.
No equality is asserted at a null history.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExtensiveGame.ObservedGame

universe uN

variable {N : Type uN}
variable {G : ObservedGame N ℝ}

namespace MeasurableKernelPresentation.KernelBehavioralProfile

variable
  {model : MeasurableHistoryModel G}
  {presentation : G.MeasurableKernelPresentation model}

/-- Marginal probability mass of the canonical complete event prefix
represented by `root`, under execution from `initialHistory`. -/
noncomputable def canonicalContinuationPrefixMass
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory root : CompleteHistory G) :
    ℝ≥0∞ :=
  profile.compiledPolicy.prefixMeasure
      model.toArena_terminalSet_measurable
      initialHistory
      (MeasurableHistoryModel.canonicalContinuationStart root)
    ({model.canonicalContinuationPrefix root} :
      Set
        (model.toArena.ContinuationPrefix
          (MeasurableHistoryModel.canonicalContinuationStart root)))

/-- Regular conditional shifted future event-path law at the canonical prefix
of `root`, under a path law started from `initialHistory`. -/
noncomputable def conditionalContinuationEventPathMeasure
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory root : CompleteHistory G) :
    Measure (ℕ → model.toArena.PathEvent) :=
  profile.compiledPolicy.conditionalTailKernel
    model.toArena_terminalSet_measurable
    initialHistory
    (MeasurableHistoryModel.canonicalContinuationStart root)
    (model.canonicalContinuationPrefix root)

/-- At a positive-mass canonical prefix, the regular conditional event-path
law equals constructive absolute-prefix continuation exactly. -/
theorem conditionalContinuationEventPathMeasure_eq_continuation
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory root : CompleteHistory G)
    [MeasurableSingletonClass
      (model.toArena.ContinuationPrefix
        (MeasurableHistoryModel.canonicalContinuationStart root))]
    (hpositive :
      profile.canonicalContinuationPrefixMass
          initialHistory root ≠
        0) :
    profile.conditionalContinuationEventPathMeasure
        initialHistory root =
      profile.continuationEventPathMeasure root := by
  unfold
    conditionalContinuationEventPathMeasure
    continuationEventPathMeasure
  apply
    profile.compiledPolicy.conditionalTailKernel_apply_eq_tailEventPathMeasureFromPrefix
      model.toArena_terminalSet_measurable
      initialHistory
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)
  simpa only [canonicalContinuationPrefixMass] using hpositive

/-- State-path projection of the conditional shifted event-path law. -/
noncomputable def conditionalContinuationStatePathMeasure
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory root : CompleteHistory G) :
    Measure (ℕ → model.toArena.State) :=
  (profile.conditionalContinuationEventPathMeasure
    initialHistory root).map
      MeasurableKernelArena.eventPathStates

/-- At a positive-mass canonical prefix, the conditional state-path law
equals constructive absolute-prefix continuation. -/
theorem conditionalContinuationStatePathMeasure_eq_continuation
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory root : CompleteHistory G)
    [MeasurableSingletonClass
      (model.toArena.ContinuationPrefix
        (MeasurableHistoryModel.canonicalContinuationStart root))]
    (hpositive :
      profile.canonicalContinuationPrefixMass
          initialHistory root ≠
        0) :
    profile.conditionalContinuationStatePathMeasure
        initialHistory root =
      profile.continuationStatePathMeasure root := by
  unfold
    conditionalContinuationStatePathMeasure
    continuationStatePathMeasure
    MeasurableKernelArena.EventHistoryActionPolicy.tailStatePathMeasureFromPrefix
  rw [
    profile.conditionalContinuationEventPathMeasure_eq_continuation
      initialHistory root hpositive]
  rfl

end MeasurableKernelPresentation.KernelBehavioralProfile

namespace MeasurableHistoryModel.BoundedPathUtility

variable
  {model : MeasurableHistoryModel G}
  (evaluation : MeasurableHistoryModel.BoundedPathUtility model)

/-- Expected bounded path utility under the conditional shifted state-path
law at one canonical history prefix. -/
noncomputable def conditionalContinuationExpectedUtility
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory root : CompleteHistory G)
    (i : N) :
    ℝ :=
  ∫ path, evaluation.utility i path
    ∂profile.conditionalContinuationStatePathMeasure
      initialHistory root

/-- At a positive-mass canonical prefix, conditional expected utility equals
constructive absolute-prefix continuation expected utility. -/
theorem conditionalContinuationExpectedUtility_eq_continuation
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory root : CompleteHistory G)
    [MeasurableSingletonClass
      (model.toArena.ContinuationPrefix
        (MeasurableHistoryModel.canonicalContinuationStart root))]
    (hpositive :
      profile.canonicalContinuationPrefixMass
          initialHistory root ≠
        0)
    (i : N) :
    evaluation.conditionalContinuationExpectedUtility
        profile initialHistory root i =
      evaluation.continuationExpectedUtility
        profile root i := by
  unfold
    conditionalContinuationExpectedUtility
    continuationExpectedUtility
  rw [
    profile.conditionalContinuationStatePathMeasure_eq_continuation
      initialHistory root hpositive]

end MeasurableHistoryModel.BoundedPathUtility

end ExtensiveGame.ObservedGame
