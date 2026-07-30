/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Arena
import EconCSLib.Math.Probability.PMF.ToMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Kernel.Execution — terminal-aware measurable-kernel execution

One-step policy-controlled execution for `MeasurableKernelArena`.

A policy is a measurable kernel into the total dependent action bundle.  It
is a probability measure concentrated on the current state's legal-action
fiber at nonterminal states, and the zero measure at terminal states.  The
resulting state-step kernel absorbs terminal states with a Dirac law and
composes the policy kernel with the arena transition elsewhere.

## Main definitions

* `MeasurableKernelArena.ActionPolicy` — measurable legal action laws with
  explicit terminal behavior.
* `ActionPolicy.actionStepKernel` — action selection followed by transition.
* `ActionPolicy.stepKernel` — normalized terminal-absorbing execution.
* `KernelArena.Policy.toMeasurable` — exact embedding of discrete policies.

## Main results

* `ActionPolicy.stepKernel_isMarkov` — stopped execution is normalized.
* `ActionPolicy.ae_mem_actionFiber` — policy legality holds almost surely.
* `KernelArena.Policy.toMeasurable_stepKernel_apply_nonterminal` — the
  analytic step law exactly recovers the existing PMF step law, with no
  countability assumption on the action carrier and no public decidability
  assumption on terminality.

This module deliberately stops at one-step execution.  Finite and infinite
analytic trajectory laws require a separate construction and audit. The
discrete embedding is noncomputable and performs its terminal split
classically; it is not an executable terminal classifier.
-/

open MeasureTheory ProbabilityTheory

universe uS uA

namespace MeasurableKernelArena

/-- States with no legal action. -/
def terminalSet (A : MeasurableKernelArena) : Set A.State :=
  {state | IsEmpty (A.Action state)}

/-- Bundled legal actions based at a particular state. -/
def actionFiber (A : MeasurableKernelArena) (state : A.State) :
    Set A.ActionBundle :=
  {stateAction | stateAction.1 = state}

theorem measurableSet_actionFiber (A : MeasurableKernelArena)
    [MeasurableSingletonClass A.State] (state : A.State) :
    MeasurableSet (A.actionFiber state) := by
  exact A.stateProjection_measurable
    (measurableSet_singleton state)

/-- A terminal-aware measurable policy.

At terminal states its action measure is zero.  At nonterminal states it is a
probability measure concentrated on the dependent action fiber of the current
state. -/
structure ActionPolicy (A : MeasurableKernelArena) where
  /-- A measurable, possibly killed, kernel into bundled legal actions. -/
  kernel : Kernel A.State A.ActionBundle
  /-- No action mass is produced at terminal states. -/
  terminal_zero :
    ∀ state, IsEmpty (A.Action state) → kernel state = 0
  /-- Action mass is normalized at nonterminal states. -/
  nonterminal_isProbability :
    ∀ state, ¬ IsEmpty (A.Action state) →
      IsProbabilityMeasure (kernel state)
  /-- At nonterminal states, the selected bundled action is based at the
  current state almost surely.

  This is stated directly in the almost-everywhere filter.  The action fiber
  need not be measurable when state singletons are not measurable, so the
  numerically weaker outer-measure equation `kernel state fiber = 1` is not a
  sound legality certificate in the general analytic model. -/
  legal :
    ∀ state, ¬ IsEmpty (A.Action state) →
      ∀ᵐ stateAction ∂kernel state,
        stateAction ∈ A.actionFiber state

namespace ActionPolicy

variable {A : MeasurableKernelArena}

/-- The policy chooses a legal bundled action almost surely at each
nonterminal state. -/
theorem ae_mem_actionFiber (policy : A.ActionPolicy)
    (state : A.State) (hnonterminal : ¬ IsEmpty (A.Action state)) :
    ∀ᵐ stateAction ∂policy.kernel state,
      stateAction ∈ A.actionFiber state := by
  exact policy.legal state hnonterminal

/-- On state spaces with measurable singletons, genuine almost-sure legality
recovers the familiar measure-one action-fiber equation. -/
theorem legal_mass_one (policy : A.ActionPolicy)
    [MeasurableSingletonClass A.State]
    (state : A.State) (hnonterminal : ¬ IsEmpty (A.Action state)) :
    policy.kernel state (A.actionFiber state) = 1 := by
  letI : IsProbabilityMeasure (policy.kernel state) :=
    policy.nonterminal_isProbability state hnonterminal
  have hmeasure :=
    (ae_mem_iff_measure_eq
      (A.measurableSet_actionFiber state).nullMeasurableSet).mp
        (policy.ae_mem_actionFiber state hnonterminal)
  simpa using hmeasure

/-- Compose the policy's legal-action law with the arena transition. -/
noncomputable def actionStepKernel (policy : A.ActionPolicy) :
    Kernel A.State A.State :=
  A.transition ∘ₖ policy.kernel

/-- Terminal-absorbing one-step execution.

The measurable terminal-set proof is explicit because measurability of
dependent-action emptiness does not follow from the arena fields alone. -/
noncomputable def stepKernel (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) :
    Kernel A.State A.State := by
  classical
  exact Kernel.piecewise hterminal Kernel.id policy.actionStepKernel

instance stepKernel_isMarkov (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) :
    IsMarkovKernel (policy.stepKernel hterminal) := by
  classical
  constructor
  intro state
  rw [stepKernel, Kernel.piecewise_apply]
  split_ifs with hstate
  · infer_instance
  · have hnonterminal :
        ¬ IsEmpty (A.Action state) := by
      simpa only [terminalSet, Set.mem_setOf_eq] using hstate
    change
      IsProbabilityMeasure
        ((policy.kernel state).bind A.transition)
    letI : IsProbabilityMeasure (policy.kernel state) :=
      policy.nonterminal_isProbability state hnonterminal
    exact MeasureTheory.isProbabilityMeasure_bind
      A.transition.aemeasurable
      (Filter.Eventually.of_forall fun stateAction => inferInstance)

@[simp]
theorem stepKernel_apply_terminal (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (state : A.State) (hstate : IsEmpty (A.Action state)) :
    policy.stepKernel hterminal state = Measure.dirac state := by
  classical
  rw [stepKernel, Kernel.piecewise_apply, if_pos]
  · exact Kernel.id_apply state
  · exact hstate

@[simp]
theorem stepKernel_apply_nonterminal (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (state : A.State) (hstate : ¬ IsEmpty (A.Action state)) :
    policy.stepKernel hterminal state =
      (policy.kernel state).bind A.transition := by
  classical
  rw [stepKernel, Kernel.piecewise_apply, if_neg]
  · rfl
  · exact hstate

end ActionPolicy

end MeasurableKernelArena

namespace KernelArena

/-- The killed analytic action kernel induced by a discrete policy. -/
noncomputable def Policy.toMeasurableKernel {A : KernelArena}
    (policy : A.Policy) :
    @Kernel A.State (Σ state, A.Action state) ⊤ ⊤ := by
  classical
  letI : MeasurableSpace A.State := ⊤
  letI : MeasurableSpace (Σ state, A.Action state) := ⊤
  exact
    { toFun := fun state =>
        if hterminal : IsEmpty (A.Action state) then
          0
        else
          @PMF.toMeasure (Σ state, A.Action state) ⊤
            ((policy state hterminal).map fun action =>
              (⟨state, action⟩ : Σ state, A.Action state))
      measurable' := by
        exact fun _ _ => MeasurableSpace.measurableSet_top }

@[simp]
theorem Policy.toMeasurableKernel_apply_terminal
    {A : KernelArena}
    (policy : A.Policy)
    (state : A.State) (hstate : IsEmpty (A.Action state)) :
    policy.toMeasurableKernel state = 0 := by
  classical
  simp [Policy.toMeasurableKernel, hstate]

@[simp]
theorem Policy.toMeasurableKernel_apply_nonterminal
    {A : KernelArena}
    (policy : A.Policy)
    (state : A.State) (hstate : ¬ IsEmpty (A.Action state)) :
    policy.toMeasurableKernel state =
      @PMF.toMeasure (Σ state, A.Action state) ⊤
        ((policy state hstate).map fun action =>
          (⟨state, action⟩ : Σ state, A.Action state)) := by
  classical
  simp [Policy.toMeasurableKernel, hstate]

/-- Embed a discrete terminal-aware policy as an analytic action policy. -/
noncomputable def Policy.toMeasurable {A : KernelArena}
    (policy : A.Policy) :
    A.toMeasurable.ActionPolicy := by
  classical
  exact
    { kernel := policy.toMeasurableKernel
      terminal_zero := by
        intro state hterminal
        exact policy.toMeasurableKernel_apply_terminal state hterminal
      nonterminal_isProbability := by
        intro state hnonterminal
        change ¬ IsEmpty (A.Action state) at hnonterminal
        change IsProbabilityMeasure
          (if hterminal : IsEmpty (A.Action state) then
            0
          else
            @PMF.toMeasure (Σ state, A.Action state) ⊤
              ((policy state hterminal).map fun action =>
                (⟨state, action⟩ : Σ state, A.Action state)))
        rw [dif_neg hnonterminal]
        infer_instance
      legal := by
        intro state hnonterminal
        change ¬ IsEmpty (A.Action state) at hnonterminal
        change
          ∀ᵐ stateAction
              ∂(if hterminal : IsEmpty (A.Action state) then
                0
              else
                @PMF.toMeasure (Σ state, A.Action state) ⊤
                  ((policy state hterminal).map fun action =>
                    (⟨state, action⟩ :
                      Σ state, A.Action state))),
            stateAction.1 = state
        rw [dif_neg hnonterminal]
        refine
          (ae_iff_measure_eq
            (μ :=
              @PMF.toMeasure (Σ state, A.Action state) ⊤
                ((policy state hnonterminal).map fun action =>
                  (⟨state, action⟩ :
                    Σ state, A.Action state)))
            (p := fun stateAction => stateAction.1 = state)
            (show
              @MeasurableSet (Σ state, A.Action state) ⊤
                {stateAction | stateAction.1 = state} from
              MeasurableSpace.measurableSet_top
            ).nullMeasurableSet).2 ?_
        rw [measure_univ]
        apply
          (@PMF.toMeasure_apply_eq_one_iff
            (Σ state, A.Action state) ⊤
            ((policy state hnonterminal).map fun action =>
              (⟨state, action⟩ : Σ state, A.Action state))
            {stateAction | stateAction.1 = state}
            MeasurableSpace.measurableSet_top).2
        intro stateAction hsupport
        obtain ⟨action, _, rfl⟩ :=
          (PMF.mem_support_map_iff
            (fun action =>
              (⟨state, action⟩ : Σ state, A.Action state))
            (policy state hnonterminal) stateAction).mp hsupport
        rfl }

/-- Terminal states form a measurable set after the discrete embedding. -/
theorem toMeasurable_measurableSet_terminalSet (A : KernelArena) :
    MeasurableSet A.toMeasurable.terminalSet :=
  MeasurableSpace.measurableSet_top

@[simp]
theorem Policy.toMeasurable_kernel_apply_nonterminal
    {A : KernelArena}
    (policy : A.Policy)
    (state : A.State) (hstate : ¬ IsEmpty (A.Action state)) :
    policy.toMeasurable.kernel state =
      @PMF.toMeasure (Σ state, A.Action state) ⊤
        ((policy state hstate).map fun action =>
          (⟨state, action⟩ : Σ state, A.Action state)) := by
  exact policy.toMeasurableKernel_apply_nonterminal state hstate

/-- Analytic one-step execution recovers the old PMF step law exactly at
nonterminal states, without assuming a countable action carrier. -/
theorem Policy.toMeasurable_stepKernel_apply_nonterminal
    {A : KernelArena}
    (policy : A.Policy)
    (state : A.State) (hstate : ¬ IsEmpty (A.Action state)) :
    policy.toMeasurable.stepKernel
        A.toMeasurable_measurableSet_terminalSet state =
      @PMF.toMeasure A.State ⊤
        (A.stepLaw policy state hstate) := by
  letI : MeasurableSpace A.State := ⊤
  letI : MeasurableSpace (Σ state, A.Action state) := ⊤
  rw [MeasurableKernelArena.ActionPolicy.stepKernel_apply_nonterminal
    _ _ _ hstate]
  rw [Policy.toMeasurable_kernel_apply_nonterminal policy state hstate]
  change
    (@PMF.toMeasure (Σ state, A.Action state) ⊤
      ((policy state hstate).map fun action =>
        (⟨state, action⟩ : Σ state, A.Action state))).bind
      (fun stateAction =>
        @PMF.toMeasure A.State ⊤
          (A.next stateAction.1 stateAction.2)) =
      @PMF.toMeasure A.State ⊤
        (A.stepLaw policy state hstate)
  rw [← PMF.toMeasure_bind_eq_bind_toMeasure]
  · rw [PMF.bind_map]
    rfl
  · exact A.toMeasurable.transition.aemeasurable

/-- The embedded analytic execution absorbs a discrete terminal state with
exactly the same Dirac law used by the stopped PMF execution. -/
theorem Policy.toMeasurable_stepKernel_apply_terminal
    {A : KernelArena}
    (policy : A.Policy)
    (state : A.State) (hstate : IsEmpty (A.Action state)) :
    policy.toMeasurable.stepKernel
        A.toMeasurable_measurableSet_terminalSet state =
      @Measure.dirac A.State ⊤ state :=
  MeasurableKernelArena.ActionPolicy.stepKernel_apply_terminal
    _ _ _ hstate

end KernelArena
