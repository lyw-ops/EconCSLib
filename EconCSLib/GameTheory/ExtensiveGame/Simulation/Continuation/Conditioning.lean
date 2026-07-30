/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Path
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Continuation.Conditioning — positive-prefix conditional compatibility

Constructive absolute-prefix continuation is defined at every supplied event
prefix, including prefixes having probability zero under a path law. Regular
conditional distributions, by contrast, are determined only almost
everywhere.

This module proves the mathematically safe compatibility statement:

* the regular conditional distribution of the shifted future event path,
  given the complete finite prefix, agrees almost everywhere with the
  constructive absolute-prefix continuation kernel;
* at a particular prefix whose singleton has positive marginal probability,
  the agreement is pointwise;
* at such an atom, the continuation law has the usual normalized joint-mass
  formula;
* when the prefix mass is zero, that normalized formula collapses to zero and
  cannot equal the constructive probability law.

The regular conditional distribution requires a standard Borel future-path
space. No pointwise claim is made at null prefixes.
-/

open MeasureTheory ProbabilityTheory

namespace MeasurableKernelArena

variable {A : MeasurableKernelArena}

namespace EventHistoryActionPolicy

/-- Kernel assigning to each complete prefix through `start` its constructive
absolute-clock shifted future event-path law. -/
noncomputable def continuationTailKernel
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ) :
    Kernel
      (A.ContinuationPrefix start)
      (ℕ → A.PathEvent) :=
  (Kernel.traj
    (policy.pathStepKernel hterminal)
    start).map
      (tailEventPath start)

/-- The constructive continuation-tail kernel is Markov. -/
instance continuationTailKernel_isMarkov
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ) :
    IsMarkovKernel
      (policy.continuationTailKernel
        hterminal start) := by
  unfold continuationTailKernel
  exact
    ProbabilityTheory.Kernel.IsMarkovKernel.map _
      (measurable_tailEventPath (A := A) start)

/-- Evaluating the continuation-tail kernel is exactly the previously
defined constructive tail law. -/
@[simp]
theorem continuationTailKernel_apply
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    policy.continuationTailKernel
        hterminal start initialPrefix =
      policy.tailEventPathMeasureFromPrefix
        hterminal start initialPrefix := by
  rw [
    continuationTailKernel,
    Kernel.map_apply _
      (measurable_tailEventPath (A := A) start)]
  rfl

/-- Regular conditional distribution of the shifted future event path given
the complete prefix through `start` under a time-zero path law. -/
noncomputable def conditionalTailKernel
    [StandardBorelSpace (ℕ → A.PathEvent)]
    [Nonempty (ℕ → A.PathEvent)]
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (start : ℕ) :
    Kernel
      (A.ContinuationPrefix start)
      (ℕ → A.PathEvent) :=
  condDistrib
    (tailEventPath start)
    (Preorder.frestrictLe start)
    (policy.pathMeasure hterminal initialState)

/-- The joint law of the complete prefix and shifted future path factors as
the prefix marginal followed by the constructive continuation-tail kernel.
-/
theorem pathMeasure_map_prefix_tail_eq_compProd
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (start : ℕ) :
    (policy.pathMeasure hterminal initialState).map
        (fun path =>
          (Preorder.frestrictLe start path,
            tailEventPath start path)) =
      policy.prefixMeasure
          hterminal initialState start ⊗ₘ
        policy.continuationTailKernel
          hterminal start := by
  rw [policy.prefixMeasure_eq_partialTraj]
  unfold continuationTailKernel
  rw [
    Measure.compProd_map
      (measurable_tailEventPath (A := A) start)]
  rw [
    Kernel.partialTraj_compProd_traj
      (κ := policy.pathStepKernel hterminal)
      (a := 0) (b := start)
      (Nat.zero_le start)
      (fun _ : Finset.Iic 0 =>
        A.initialEvent initialState)]
  unfold pathMeasure
  rw [Measure.map_map]
  · rfl
  · exact
      Measurable.prod
        measurable_fst
        ((measurable_tailEventPath (A := A) start).comp
          measurable_snd)
  · exact
      Measurable.prod
        (by fun_prop)
        measurable_id

/-- The conditional shifted-future kernel agrees almost everywhere, under
the finite-prefix marginal, with constructive absolute-prefix continuation.
-/
theorem conditionalTailKernel_ae_eq_continuationTailKernel
    [StandardBorelSpace (ℕ → A.PathEvent)]
    [Nonempty (ℕ → A.PathEvent)]
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (start : ℕ) :
    policy.conditionalTailKernel
        hterminal initialState start
      =ᵐ[policy.prefixMeasure
        hterminal initialState start]
    policy.continuationTailKernel
      hterminal start := by
  unfold conditionalTailKernel
  have hfactor :=
    policy.pathMeasure_map_prefix_tail_eq_compProd
      hterminal initialState start
  apply
    condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := policy.pathMeasure hterminal initialState)
      (X := Preorder.frestrictLe start)
      (Y := tailEventPath start)
      (κ := policy.continuationTailKernel
        hterminal start)
  · fun_prop
  · exact measurable_tailEventPath (A := A) start
  · simpa only [prefixMeasure] using hfactor

/-- An almost-everywhere kernel identity holds pointwise at every prefix atom
of nonzero marginal mass. -/
theorem conditionalTailKernel_eq_continuationTailKernel_of_prefix_ne_zero
    [StandardBorelSpace (ℕ → A.PathEvent)]
    [Nonempty (ℕ → A.PathEvent)]
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (start : ℕ)
    [MeasurableSingletonClass (A.ContinuationPrefix start)]
    (initialPrefix : A.ContinuationPrefix start)
    (hpositive :
      policy.prefixMeasure hterminal initialState start
          ({initialPrefix} :
            Set (A.ContinuationPrefix start)) ≠
        0) :
    policy.conditionalTailKernel
        hterminal initialState start initialPrefix =
      policy.continuationTailKernel
        hterminal start initialPrefix := by
  have hae :=
    policy.conditionalTailKernel_ae_eq_continuationTailKernel
      hterminal initialState start
  change
    {candidate |
      policy.conditionalTailKernel
          hterminal initialState start candidate =
        policy.continuationTailKernel
          hterminal start candidate} ∈
      ae (policy.prefixMeasure
        hterminal initialState start)
    at hae
  rw [mem_ae_iff] at hae
  by_contra hne
  have hsubset :
      ({initialPrefix} :
          Set (A.ContinuationPrefix start)) ⊆
        {candidate |
          policy.conditionalTailKernel
              hterminal initialState start candidate =
            policy.continuationTailKernel
              hterminal start candidate}ᶜ := by
    intro candidate hprefix
    rw [Set.mem_singleton_iff] at hprefix
    subst candidate
    exact hne
  exact
    hpositive
      (measure_mono_null hsubset hae)

/-- At a positive-probability prefix atom, the regular conditional tail law
is exactly the constructive shifted continuation path law. -/
theorem conditionalTailKernel_apply_eq_tailEventPathMeasureFromPrefix
    [StandardBorelSpace (ℕ → A.PathEvent)]
    [Nonempty (ℕ → A.PathEvent)]
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (start : ℕ)
    [MeasurableSingletonClass (A.ContinuationPrefix start)]
    (initialPrefix : A.ContinuationPrefix start)
    (hpositive :
      policy.prefixMeasure hterminal initialState start
          ({initialPrefix} :
            Set (A.ContinuationPrefix start)) ≠
        0) :
    policy.conditionalTailKernel
        hterminal initialState start initialPrefix =
      policy.tailEventPathMeasureFromPrefix
        hterminal start initialPrefix := by
  rw [
    policy.conditionalTailKernel_eq_continuationTailKernel_of_prefix_ne_zero
      hterminal initialState start initialPrefix hpositive]
  exact
    policy.continuationTailKernel_apply
      hterminal start initialPrefix

/-- At a positive prefix atom, constructive continuation satisfies the usual
normalized joint-mass formula for every future-path event.
-/
theorem tailEventPathMeasureFromPrefix_apply_eq_normalized_joint
    [StandardBorelSpace (ℕ → A.PathEvent)]
    [Nonempty (ℕ → A.PathEvent)]
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (start : ℕ)
    [MeasurableSingletonClass (A.ContinuationPrefix start)]
    (initialPrefix : A.ContinuationPrefix start)
    (hpositive :
      policy.prefixMeasure hterminal initialState start
          ({initialPrefix} :
            Set (A.ContinuationPrefix start)) ≠
        0)
    (futureEvent : Set (ℕ → A.PathEvent)) :
    policy.tailEventPathMeasureFromPrefix
        hterminal start initialPrefix futureEvent =
      (policy.prefixMeasure
          hterminal initialState start
          ({initialPrefix} :
            Set (A.ContinuationPrefix start)))⁻¹ *
        (policy.pathMeasure
          hterminal initialState).map
            (fun path =>
              (Preorder.frestrictLe start path,
                tailEventPath start path))
            (({initialPrefix} :
                Set (A.ContinuationPrefix start)) ×ˢ
              futureEvent) := by
  rw [
    ← policy.conditionalTailKernel_apply_eq_tailEventPathMeasureFromPrefix
      hterminal initialState start initialPrefix hpositive]
  exact
    condDistrib_apply_of_ne_zero
      (μ := policy.pathMeasure hterminal initialState)
      (X := Preorder.frestrictLe start)
      (Y := tailEventPath start)
      (measurable_tailEventPath (A := A) start)
      initialPrefix
      (by
        simpa only [prefixMeasure] using hpositive)
      futureEvent

/-- The joint prefix/future law gives the event “this prefix and any future”
exactly the prefix marginal mass. -/
theorem pathMeasure_map_prefix_tail_singleton_prod_univ
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (start : ℕ)
    [MeasurableSingletonClass (A.ContinuationPrefix start)]
    (initialPrefix : A.ContinuationPrefix start) :
    (policy.pathMeasure
        hterminal initialState).map
          (fun path =>
            (Preorder.frestrictLe start path,
              tailEventPath start path))
          (({initialPrefix} :
              Set (A.ContinuationPrefix start)) ×ˢ
            (Set.univ : Set (ℕ → A.PathEvent))) =
      policy.prefixMeasure
        hterminal initialState start
        ({initialPrefix} :
          Set (A.ContinuationPrefix start)) := by
  rw [
    Measure.map_apply
      (Measurable.prod
        (by fun_prop)
        (measurable_tailEventPath (A := A) start))
      ((measurableSet_singleton initialPrefix).prod
        MeasurableSet.univ)]
  rw [
    prefixMeasure,
    Measure.map_apply
      (by fun_prop)
      (measurableSet_singleton initialPrefix)]
  congr 1
  ext path
  simp

/-- If the prefix atom has zero mass, the normalized joint-mass expression
is identically zero and therefore cannot represent the constructive
continuation probability law.
-/
theorem not_normalized_joint_formula_of_prefix_eq_zero
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (start : ℕ)
    [MeasurableSingletonClass (A.ContinuationPrefix start)]
    (initialPrefix : A.ContinuationPrefix start)
    (hzero :
      policy.prefixMeasure hterminal initialState start
          ({initialPrefix} :
            Set (A.ContinuationPrefix start)) =
        0) :
    ¬ ∀ futureEvent : Set (ℕ → A.PathEvent),
      policy.tailEventPathMeasureFromPrefix
          hterminal start initialPrefix futureEvent =
        (policy.prefixMeasure
            hterminal initialState start
            ({initialPrefix} :
              Set (A.ContinuationPrefix start)))⁻¹ *
          (policy.pathMeasure
            hterminal initialState).map
              (fun path =>
                (Preorder.frestrictLe start path,
                  tailEventPath start path))
              (({initialPrefix} :
                  Set (A.ContinuationPrefix start)) ×ˢ
                futureEvent) := by
  intro hall
  have huniv :=
    hall (Set.univ : Set (ℕ → A.PathEvent))
  have hleft :
      policy.tailEventPathMeasureFromPrefix
          hterminal start initialPrefix
          (Set.univ : Set (ℕ → A.PathEvent)) =
        1 := by
    simp
  rw [
    hleft,
    hzero,
    policy.pathMeasure_map_prefix_tail_singleton_prod_univ
      hterminal initialState start initialPrefix,
    hzero]
      at huniv
  simp at huniv

end EventHistoryActionPolicy

end MeasurableKernelArena
