/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Execution

/-!
# Kernel.Endpoint — finite-horizon measurable endpoint laws

Finite iteration of the terminal-absorbing state-step kernel from
`MeasurableKernelExecution`.

The declarations here describe only the state law at a selected finite
horizon.  They do not construct a joint law of the intermediate states and are
therefore deliberately named endpoint kernels and measures, not trajectories.

## Main definitions

* `ActionPolicy.endpointKernel` — the stopped state kernel after a finite
  number of steps.
* `ActionPolicy.endpointMeasure` — that kernel evaluated at an initial state.

## Main results

* `ActionPolicy.endpointKernel_isMarkov` — every finite endpoint kernel is
  normalized.
* `ActionPolicy.endpointMeasure_succ` — the Chapman--Kolmogorov successor
  recursion.
* `ActionPolicy.endpointMeasure_terminal` — terminal states remain Dirac at
  every horizon.
* `KernelArena.Policy.toMeasurable_endpointMeasure` — exact recovery of the
  existing discrete `stateLawFrom` PMF at every finite horizon.
-/

open MeasureTheory ProbabilityTheory

universe uS uA

namespace MeasurableKernelArena

namespace ActionPolicy

variable {A : MeasurableKernelArena}

/-- The state kernel after exactly `horizon` terminal-absorbing steps. -/
noncomputable def endpointKernel (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) :
    ℕ → Kernel A.State A.State
  | 0 => Kernel.id
  | horizon + 1 =>
      policy.endpointKernel hterminal horizon ∘ₖ
        policy.stepKernel hterminal

@[simp]
theorem endpointKernel_zero (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) :
    policy.endpointKernel hterminal 0 = Kernel.id := by
  rfl

theorem endpointKernel_succ (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (horizon : ℕ) :
    policy.endpointKernel hterminal horizon.succ =
      policy.endpointKernel hterminal horizon ∘ₖ
        policy.stepKernel hterminal := by
  rfl

@[simp]
theorem endpointKernel_one (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) :
    policy.endpointKernel hterminal 1 =
      policy.stepKernel hterminal := by
  rw [show 1 = Nat.succ 0 by rfl, endpointKernel_succ,
    endpointKernel_zero, Kernel.id_comp]

/-- Finite endpoint kernels satisfy the Chapman--Kolmogorov composition law:
run `first` steps and then `second` steps. -/
theorem endpointKernel_add (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (first second : ℕ) :
    policy.endpointKernel hterminal (first + second) =
      policy.endpointKernel hterminal second ∘ₖ
        policy.endpointKernel hterminal first := by
  induction first with
  | zero =>
      rw [Nat.zero_add, endpointKernel_zero, Kernel.comp_id]
  | succ first ih =>
      rw [Nat.succ_add, endpointKernel_succ, ih,
        endpointKernel_succ, Kernel.comp_assoc]

instance endpointKernel_isMarkov (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (horizon : ℕ) :
    IsMarkovKernel (policy.endpointKernel hterminal horizon) := by
  induction horizon with
  | zero =>
      rw [endpointKernel_zero]
      infer_instance
  | succ horizon ih =>
      letI : IsMarkovKernel
          (policy.endpointKernel hterminal horizon) := ih
      rw [endpointKernel_succ]
      infer_instance

/-- The endpoint law from a particular initial state. -/
noncomputable abbrev endpointMeasure (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (horizon : ℕ) (state : A.State) :
    Measure A.State :=
  policy.endpointKernel hterminal horizon state

@[simp]
theorem endpointMeasure_zero (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (state : A.State) :
    policy.endpointMeasure hterminal 0 state =
      Measure.dirac state := by
  rw [endpointMeasure, endpointKernel_zero, Kernel.id_apply]

/-- Successor endpoint laws satisfy the Chapman--Kolmogorov recursion: take
one stopped step, then run the remaining horizon. -/
theorem endpointMeasure_succ (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (horizon : ℕ) (state : A.State) :
    policy.endpointMeasure hterminal horizon.succ state =
      (policy.stepKernel hterminal state).bind
        (policy.endpointKernel hterminal horizon) := by
  rw [endpointMeasure, endpointKernel_succ]
  rfl

/-- Measure-level Chapman--Kolmogorov equation for finite endpoints. -/
theorem endpointMeasure_add (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (first second : ℕ) (state : A.State) :
    policy.endpointMeasure hterminal (first + second) state =
      (policy.endpointMeasure hterminal first state).bind
        (policy.endpointKernel hterminal second) := by
  rw [endpointMeasure, endpointKernel_add]
  rfl

/-- Equivalent successor recursion obtained by taking the existing endpoint
law and then one more stopped step. -/
theorem endpointMeasure_succ_right (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (horizon : ℕ) (state : A.State) :
    policy.endpointMeasure hterminal horizon.succ state =
      (policy.endpointMeasure hterminal horizon state).bind
        (policy.stepKernel hterminal) := by
  rw [show horizon.succ = horizon + 1 by omega,
    endpointMeasure_add, endpointKernel_one]

/-- A terminal state remains a Dirac endpoint at every horizon. -/
theorem endpointMeasure_terminal (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (horizon : ℕ) (state : A.State)
    (hstate : IsEmpty (A.Action state)) :
    policy.endpointMeasure hterminal horizon state =
      Measure.dirac state := by
  induction horizon with
  | zero =>
      exact policy.endpointMeasure_zero hterminal state
  | succ horizon ih =>
      rw [policy.endpointMeasure_succ hterminal horizon state]
      rw [policy.stepKernel_apply_terminal hterminal state hstate]
      rw [Measure.dirac_bind
        (policy.endpointKernel hterminal horizon).measurable]
      exact ih

end ActionPolicy

end MeasurableKernelArena

namespace KernelArena

/-- Every finite analytic endpoint of an embedded discrete policy is exactly
the measure associated to the existing stopped PMF endpoint law. -/
theorem Policy.toMeasurable_endpointMeasure
    {A : KernelArena}
    (policy : A.Policy) (horizon : ℕ) (state : A.State) :
    policy.toMeasurable.endpointMeasure
        A.toMeasurable_measurableSet_terminalSet horizon state =
      @PMF.toMeasure A.State ⊤
        (A.stateLawFrom policy horizon state) := by
  letI : MeasurableSpace A.State := ⊤
  letI : MeasurableSpace (Σ state, A.Action state) := ⊤
  induction horizon generalizing state with
  | zero =>
      rw [MeasurableKernelArena.ActionPolicy.endpointMeasure_zero]
      change
        Measure.dirac state =
          @PMF.toMeasure A.State ⊤ (PMF.pure state)
      exact (@PMF.toMeasure_pure A.State state ⊤).symm
  | succ horizon ih =>
      by_cases hterminal : IsEmpty (A.Action state)
      · rw [MeasurableKernelArena.ActionPolicy.endpointMeasure_terminal
          _ _ _ _ hterminal]
        simp only [stateLawFrom, dif_pos hterminal]
        change
          Measure.dirac state =
            @PMF.toMeasure A.State ⊤ (PMF.pure state)
        exact (@PMF.toMeasure_pure A.State state ⊤).symm
      · rw [MeasurableKernelArena.ActionPolicy.endpointMeasure_succ]
        rw [Policy.toMeasurable_stepKernel_apply_nonterminal
          policy state hterminal]
        have hfunction :
            (fun nextState =>
              @PMF.toMeasure A.State ⊤
                (A.stateLawFrom policy horizon nextState)) =
            (policy.toMeasurable.endpointKernel
              A.toMeasurable_measurableSet_terminalSet horizon) := by
          funext nextState
          exact (ih nextState).symm
        rw [← hfunction]
        change
          (@PMF.toMeasure A.State ⊤
            (A.stepLaw policy state hterminal)).bind
              (fun nextState =>
                @PMF.toMeasure A.State ⊤
                  (A.stateLawFrom policy horizon nextState)) =
            @PMF.toMeasure A.State ⊤
              (A.stateLawFrom policy horizon.succ state)
        rw [← PMF.toMeasure_bind_eq_bind_toMeasure]
        · simp only [stateLawFrom, dif_neg hterminal]
        · rw [hfunction]
          exact
            (policy.toMeasurable.endpointKernel
              A.toMeasurable_measurableSet_terminalSet horizon).aemeasurable

end KernelArena
