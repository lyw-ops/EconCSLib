/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Endpoint
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Kernel.StatePath — infinite state paths for measurable kernel arenas

Ionescu--Tulcea path semantics for a terminal-aware
`MeasurableKernelArena.ActionPolicy`.

The stopped state-step kernel is pulled back along the latest-state projection
of each finite history.  Mathlib's Ionescu--Tulcea theorem then gives a
probability measure on infinite state paths.  The main marginal theorem proves
that coordinate `n` is exactly the finite `endpointMeasure` already audited;
embedded discrete policies therefore recover `KernelArena.stateLawFrom`
coordinate by coordinate.

## Main definitions

* `ActionPolicy.pathStepKernel` — next-state kernel on finite state histories.
* `ActionPolicy.pathMeasure` — probability measure on `ℕ → A.State`.
* `ActionPolicy.prefixMeasure` — joint finite-prefix law.
* `ActionPolicy.coordinateMeasure` — one-coordinate marginal.

## Main results

* `ActionPolicy.pathMeasure_eq_trajMeasure` — identification with Mathlib's
  Dirac-initialized `Kernel.trajMeasure`.
* `ActionPolicy.coordinateMeasure_eq_endpointMeasure` — exact coordinate
  marginal theorem.
* `KernelArena.Policy.toMeasurable_coordinateMeasure` — exact recovery of the
  old stopped PMF endpoint law.
* `ActionPolicy.ae_path_eq_const_of_terminal` — terminal starts give the
  constant path almost surely when state singletons are measurable.

Time is the natural-number event index.  This module does not define
continuous physical time, càdlàg paths, observed strategies, or equilibrium
semantics.
-/

open MeasureTheory ProbabilityTheory

universe uS uA

namespace MeasurableKernelArena

variable {A : MeasurableKernelArena}

/-- The time-indexed state type used by the Ionescu--Tulcea construction. -/
abbrev StateAt (A : MeasurableKernelArena) (_time : ℕ) :=
  A.State

/-- Latest state in a finite history through `time`. -/
def latestState (time : ℕ)
    (history : Π _index : Finset.Iic time, A.State) :
    A.State :=
  history ⟨time, Finset.mem_Iic.mpr le_rfl⟩

/-- Reading the latest state from a finite product history is measurable. -/
theorem measurable_latestState (time : ℕ) :
    Measurable (@latestState A time) := by
  exact @measurable_pi_apply
    (Finset.Iic time) (fun _ => A.State)
    (fun _ => inferInstance)
    ⟨time, Finset.mem_Iic.mpr le_rfl⟩

namespace ActionPolicy

/-- Read the latest state of a finite history and take one stopped step. -/
noncomputable def pathStepKernel (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    Kernel
      (Π index : Finset.Iic time, StateAt A index)
      (StateAt A (time + 1)) :=
  Kernel.comap (policy.stepKernel hterminal)
    (latestState time)
    (measurable_latestState time)

/-- Every finite-history next-state kernel is Markov. -/
instance pathStepKernel_isMarkov (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    IsMarkovKernel (policy.pathStepKernel hterminal time) := by
  rw [pathStepKernel]
  infer_instance

/-- Infinite discrete-event state-path law from an initial state. -/
noncomputable def pathMeasure (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    Measure (ℕ → A.State) :=
  Kernel.traj (policy.pathStepKernel hterminal) 0
    (fun _ => initialState)

/-- The deterministic-initial-state path law is exactly Mathlib's
`trajMeasure` started from the corresponding Dirac measure. -/
theorem pathMeasure_eq_trajMeasure (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    policy.pathMeasure hterminal initialState =
      Kernel.trajMeasure
        (X := StateAt A)
        (Measure.dirac initialState)
        (policy.pathStepKernel hterminal) := by
  rw [pathMeasure, Kernel.trajMeasure]
  rw [Measure.map_dirac' (by fun_prop)]
  change
    Kernel.traj (policy.pathStepKernel hterminal) 0
        (fun _ => initialState) =
      (Measure.dirac _).bind
        (Kernel.traj (policy.pathStepKernel hterminal) 0)
  rw [Measure.dirac_bind
    (Kernel.traj (policy.pathStepKernel hterminal) 0).measurable]
  rfl

/-- The Ionescu--Tulcea state-path law is a probability measure. -/
instance pathMeasure_isProbability (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    IsProbabilityMeasure
      (policy.pathMeasure hterminal initialState) := by
  rw [pathMeasure]
  infer_instance

/-- Marginal state law at one path coordinate. -/
noncomputable def coordinateMeasure (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    Measure A.State :=
  (policy.pathMeasure hterminal initialState).map
    (fun path => path time)

/-- Joint law of the path prefix through `time`. -/
noncomputable def prefixMeasure (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    Measure (Π _index : Finset.Iic time, A.State) :=
  (policy.pathMeasure hterminal initialState).map
    (Preorder.frestrictLe time)

/-- Ionescu--Tulcea identifies each prefix law with the corresponding
finite partial-trajectory kernel. -/
theorem prefixMeasure_eq_partialTraj (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    policy.prefixMeasure hterminal initialState time =
      Kernel.partialTraj
        (policy.pathStepKernel hterminal) 0 time
        (fun _ => initialState) := by
  rw [prefixMeasure, pathMeasure]
  exact
    @Kernel.traj_map_frestrictLe_apply
      (StateAt A) (fun _ => inferInstance)
      (policy.pathStepKernel hterminal)
      (fun _ => inferInstance)
      0 time (fun _ => initialState)

/-- Pushing the next prefix law to its latest coordinate is one history step
after the preceding prefix law. -/
theorem map_partialTraj_latest_succ (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    (Kernel.partialTraj
      (policy.pathStepKernel hterminal) 0 time.succ).map
        (latestState time.succ) =
      policy.pathStepKernel hterminal time ∘ₖ
        Kernel.partialTraj
          (policy.pathStepKernel hterminal) 0 time := by
  rw [← Kernel.partialTraj_comp_partialTraj
    (κ := policy.pathStepKernel hterminal)
    (a := 0) (b := time) (c := time.succ)
    (Nat.zero_le time) (Nat.le_succ time)]
  rw [Kernel.map_comp]
  have hlatest :
      (Kernel.partialTraj
        (policy.pathStepKernel hterminal)
        time time.succ).map (latestState time.succ) =
          policy.pathStepKernel hterminal time := by
    simpa only [Nat.succ_eq_add_one, latestState] using
      (@Kernel.map_partialTraj_succ_self
        (StateAt A) (fun _ => inferInstance)
        (policy.pathStepKernel hterminal)
        (fun _ => inferInstance)
        time)
  rw [hlatest]

/-- Composing a prefix law with the history step depends only on the latest
state marginal. -/
theorem pathStepKernel_comp (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ)
    (prefixLaw :
      Measure (Π _index : Finset.Iic time, A.State)) :
    policy.pathStepKernel hterminal time ∘ₘ prefixLaw =
      policy.stepKernel hterminal ∘ₘ
        prefixLaw.map (latestState time) := by
  rw [pathStepKernel]
  rw [← Kernel.comp_deterministic_eq_comap
    (policy.stepKernel hterminal)
    (measurable_latestState time)]
  rw [← Measure.comp_assoc]
  rw [Measure.deterministic_comp_eq_map]

/-- A coordinate marginal is the latest-state pushforward of its prefix
law. -/
theorem coordinateMeasure_eq_map_prefix (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    policy.coordinateMeasure hterminal initialState time =
      (policy.prefixMeasure hterminal initialState time).map
        (latestState time) := by
  rw [coordinateMeasure, prefixMeasure]
  rw [Measure.map_map
    (measurable_latestState time)
    (by fun_prop)]
  rfl

theorem coordinateMeasure_zero (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    policy.coordinateMeasure hterminal initialState 0 =
      Measure.dirac initialState := by
  rw [coordinateMeasure_eq_map_prefix]
  rw [prefixMeasure_eq_partialTraj]
  rw [Kernel.partialTraj_self, Kernel.id_apply]
  rw [Measure.map_dirac' (measurable_latestState 0)]
  rfl

/-- Coordinate marginals evolve by the stopped state-step kernel. -/
theorem coordinateMeasure_succ (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    policy.coordinateMeasure hterminal initialState time.succ =
      policy.stepKernel hterminal ∘ₘ
        policy.coordinateMeasure hterminal initialState time := by
  rw [coordinateMeasure_eq_map_prefix,
    prefixMeasure_eq_partialTraj]
  have hstep := congrArg
    (fun kernel =>
      kernel (fun _ : Finset.Iic 0 => initialState))
    (policy.map_partialTraj_latest_succ hterminal time)
  change
    (Kernel.partialTraj
      (policy.pathStepKernel hterminal) 0 time.succ).map
        (latestState time.succ)
        (fun _ : Finset.Iic 0 => initialState) =
      (policy.pathStepKernel hterminal time ∘ₖ
        Kernel.partialTraj
          (policy.pathStepKernel hterminal) 0 time)
        (fun _ : Finset.Iic 0 => initialState) at hstep
  rw [Kernel.map_apply _
    (measurable_latestState time.succ)] at hstep
  rw [Kernel.comp_apply] at hstep
  rw [hstep]
  rw [policy.pathStepKernel_comp hterminal time]
  rw [← prefixMeasure_eq_partialTraj]
  rw [← coordinateMeasure_eq_map_prefix]

/-- Every path coordinate marginal is exactly the corresponding finite
endpoint law. -/
theorem coordinateMeasure_eq_endpointMeasure
    (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    policy.coordinateMeasure hterminal initialState time =
      policy.endpointMeasure hterminal time initialState := by
  induction time with
  | zero =>
      rw [coordinateMeasure_zero, endpointMeasure_zero]
  | succ time ih =>
      rw [coordinateMeasure_succ, ih,
        endpointMeasure_succ_right]

/-- A terminal initial state is observed at every coordinate almost surely. -/
theorem ae_path_apply_eq_of_terminal
    (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [MeasurableSingletonClass A.State]
    (initialState : A.State)
    (hstate : IsEmpty (A.Action initialState))
    (time : ℕ) :
    ∀ᵐ path ∂policy.pathMeasure hterminal initialState,
      path time = initialState := by
  letI : IsProbabilityMeasure
      (policy.pathMeasure hterminal initialState) := inferInstance
  let event : Set (ℕ → A.State) :=
    {path | path time = initialState}
  have hevent : MeasurableSet event := by
    exact
      (@measurable_pi_apply
        ℕ (fun _ => A.State) (fun _ => inferInstance) time)
      (measurableSet_singleton initialState)
  rw [show (∀ᵐ path ∂policy.pathMeasure hterminal initialState,
      path time = initialState) =
      (∀ᵐ path ∂policy.pathMeasure hterminal initialState,
        path ∈ event) by rfl]
  rw [ae_mem_iff_measure_eq hevent.nullMeasurableSet]
  rw [measure_univ]
  change
    policy.pathMeasure hterminal initialState
      ((fun path => path time) ⁻¹' {initialState}) = 1
  rw [← Measure.map_apply (measurable_pi_apply time)
    (measurableSet_singleton initialState)]
  change
    policy.coordinateMeasure hterminal initialState time
      {initialState} = 1
  rw [coordinateMeasure_eq_endpointMeasure]
  rw [policy.endpointMeasure_terminal
    hterminal time initialState hstate]
  rw [Measure.dirac_apply' _ (measurableSet_singleton initialState)]
  simp

/-- A terminal initial state yields the constant infinite path almost surely. -/
theorem ae_path_eq_const_of_terminal
    (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [MeasurableSingletonClass A.State]
    (initialState : A.State)
    (hstate : IsEmpty (A.Action initialState)) :
    ∀ᵐ path ∂policy.pathMeasure hterminal initialState,
      path = fun _ => initialState := by
  refine (ae_all_iff.2 fun time =>
    policy.ae_path_apply_eq_of_terminal
      hterminal initialState hstate time).mono ?_
  intro path hpath
  funext time
  exact hpath time

end ActionPolicy

end MeasurableKernelArena

namespace KernelArena

/-- Every coordinate marginal of the analytic path law for an embedded
discrete policy recovers the existing stopped PMF state law exactly. -/
theorem Policy.toMeasurable_coordinateMeasure
    {A : KernelArena}
    (policy : A.Policy) (initialState : A.State) (time : ℕ) :
    policy.toMeasurable.coordinateMeasure
        A.toMeasurable_measurableSet_terminalSet
        initialState time =
      @PMF.toMeasure A.State ⊤
        (A.stateLawFrom policy time initialState) := by
  rw [MeasurableKernelArena.ActionPolicy.coordinateMeasure_eq_endpointMeasure]
  exact policy.toMeasurable_endpointMeasure time initialState

end KernelArena
