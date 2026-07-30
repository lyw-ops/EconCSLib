/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Infinite stochastic execution paths

This module extends the bounded PMF executor with a genuine probability law
on infinite, terminal-absorbing history trajectories. Its coordinate marginals
are proved equal to the existing bounded executor at every event time.

It also supplies the natural filtration, first-terminal stopping time,
almost-sure termination predicate, stopped and terminal payoffs, dominated
expectation convergence, vanishing unfinished mass, and weak convergence of
bounded stopped-payoff laws.

The path coordinate is event time (Nat), not physical clock time. Continuous-
time path regularity is deliberately outside this interface.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Arena

variable {A : Arena} {start : A.State}

/-- One terminal-absorbing stochastic history step. -/
noncomputable def absorbingStepPMF
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    PMF (A.HistoryFrom start) :=
  if hterminal : A.IsTerminal current.1 then
    PMF.pure current
  else
    (policy current hterminal).map fun action =>
      ⟨A.next current.1 action, current.2.snoc action⟩

@[simp]
theorem absorbingStepPMF_eq_stochasticHistoryPMFFrom_one
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    absorbingStepPMF policy current =
      A.stochasticHistoryPMFFrom policy current 1 := by
  by_cases hterminal : A.IsTerminal current.1
  · simp [absorbingStepPMF, hterminal]
  · rw [absorbingStepPMF, dif_neg hterminal]
    rw [A.stochasticHistoryPMFFrom_succ_of_not_terminal
      policy current 0 hterminal]
    exact (PMF.bind_pure_comp _ _).symm

noncomputable def stepKernel
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) :
    Kernel (A.HistoryFrom start) (A.HistoryFrom start) :=
  Kernel.ofFunOfCountable fun current =>
    (absorbingStepPMF policy current).toMeasure

instance stepKernel_isMarkov
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) :
    IsMarkovKernel (stepKernel policy) :=
  ⟨fun current => by
    change IsProbabilityMeasure
      ((absorbingStepPMF policy current).toMeasure)
    infer_instance⟩

@[simp]
theorem stepKernel_apply
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    stepKernel policy current =
      (absorbingStepPMF policy current).toMeasure :=
  rfl

noncomputable def trajectoryKernel
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (n : ℕ) :
    Kernel
      ((i : Finset.Iic n) → A.HistoryFrom start)
      (A.HistoryFrom start) :=
  (stepKernel policy).comap
    (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_of_countable _)

instance trajectoryKernel_isMarkov
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) (n : ℕ) :
    IsMarkovKernel (trajectoryKernel policy n) := by
  rw [trajectoryKernel]
  infer_instance

noncomputable def initialTrajectoryPrefix
    [MeasurableSpace (A.HistoryFrom start)]
    (current : A.HistoryFrom start) :
    (i : Finset.Iic 0) → A.HistoryFrom start :=
  (MeasurableEquiv.piUnique
    (fun _ : Finset.Iic 0 => A.HistoryFrom start)).symm current

noncomputable def pathLaw
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    Measure (ℕ → A.HistoryFrom start) :=
  Kernel.trajMeasure (Measure.dirac current) (trajectoryKernel policy)

instance pathLaw_isProbability
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    IsProbabilityMeasure (pathLaw policy current) := by
  rw [pathLaw]
  infer_instance

theorem stepKernel_comp_toMeasure
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (p : PMF (A.HistoryFrom start)) :
    stepKernel policy ∘ₘ p.toMeasure =
      (p.bind (absorbingStepPMF policy)).toMeasure := by
  apply Measure.ext_of_singleton
  intro endpoint
  rw [Measure.bind_apply (measurableSet_singleton endpoint)
    (Kernel.aemeasurable (stepKernel policy))]
  rw [MeasureTheory.lintegral_countable']
  rw [PMF.toMeasure_bind_apply _ _ _ (measurableSet_singleton endpoint)]
  apply tsum_congr
  intro current
  rw [stepKernel_apply]
  rw [PMF.toMeasure_apply_singleton _
    current (measurableSet_singleton current)]
  rw [PMF.toMeasure_apply_singleton _
    endpoint (measurableSet_singleton endpoint)]
  exact mul_comm _ _

noncomputable def pathMarginal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (n : ℕ) :
    Measure (A.HistoryFrom start) :=
  (pathLaw policy current).map fun path => path n

theorem pathLaw_eq_traj_apply
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    pathLaw policy current =
      Kernel.traj (trajectoryKernel policy) 0
        (initialTrajectoryPrefix current) := by
  rw [pathLaw, Kernel.trajMeasure]
  rw [Measure.map_dirac]
  rw [Measure.dirac_bind (Kernel.measurable _)]
  rfl

theorem pathMarginal_zero
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    pathMarginal policy current 0 = Measure.dirac current := by
  rw [pathMarginal, pathLaw_eq_traj_apply]
  let initial : (i : Finset.Iic 0) → A.HistoryFrom start :=
    initialTrajectoryPrefix current
  have hprefix :=
    Kernel.traj_map_frestrictLe_apply
      (X := fun _ => A.HistoryFrom start)
      (κ := trajectoryKernel policy) 0 0 initial
  rw [Kernel.partialTraj_self, Kernel.id_apply] at hprefix
  have hcoord :
      (fun path : ℕ → A.HistoryFrom start => path 0) =
        (fun x : (i : Finset.Iic 0) → A.HistoryFrom start =>
          x ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
          Preorder.frestrictLe 0 :=
    rfl
  rw [hcoord, ← Measure.map_map]
  change
    Measure.map
        (fun x : (i : Finset.Iic 0) → A.HistoryFrom start =>
          x ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
        (Measure.map (Preorder.frestrictLe 0)
          (Kernel.traj
            (X := fun _ => A.HistoryFrom start)
            (trajectoryKernel policy) 0 initial)) =
      Measure.dirac current
  rw [hprefix]
  rw [Measure.map_dirac]
  apply congrArg Measure.dirac
  change
    (MeasurableEquiv.piUnique
      (fun _ : Finset.Iic 0 => A.HistoryFrom start)).symm current
        ⟨0, Finset.mem_Iic.mpr le_rfl⟩ =
      current
  simpa only [Subsingleton.elim
    (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 0) default] using
    (MeasurableEquiv.piUnique
      (fun _ : Finset.Iic 0 => A.HistoryFrom start)).apply_symm_apply current
  all_goals fun_prop

/-- The event-time-zero coordinate of the infinite path law is the supplied
initial complete history. -/
theorem pathLaw_initial
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    (pathLaw policy current).map (fun path => path 0) =
      Measure.dirac current := by
  exact pathMarginal_zero policy current

theorem pathMarginal_succ
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (n : ℕ) :
    pathMarginal policy current (n + 1) =
      stepKernel policy ∘ₘ pathMarginal policy current n := by
  have hjoint :
      (pathLaw policy current).map (Preorder.frestrictLe n) ⊗ₘ
          trajectoryKernel policy n =
        (pathLaw policy current).map
          (fun path => (Preorder.frestrictLe n path, path (n + 1))) := by
    exact
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ => A.HistoryFrom start)
        (μ₀ := Measure.dirac current)
        (κ := trajectoryKernel policy) (a := n)
  calc
    pathMarginal policy current (n + 1) =
        ((pathLaw policy current).map
          (fun path =>
            (Preorder.frestrictLe n path, path (n + 1)))).snd := by
          rw [Measure.snd]
          rw [Measure.map_map]
          rfl
          all_goals fun_prop
    _ = ((pathLaw policy current).map
          (Preorder.frestrictLe n) ⊗ₘ
        trajectoryKernel policy n).snd := by
          rw [hjoint]
    _ = trajectoryKernel policy n ∘ₘ
        (pathLaw policy current).map
          (Preorder.frestrictLe n) := by
          rw [Measure.snd_compProd]
    _ = stepKernel policy ∘ₘ
        (pathLaw policy current).map (fun path => path n) := by
          rw [trajectoryKernel]
          rw [← Kernel.comp_deterministic_eq_comap]
          rw [← Measure.comp_assoc]
          rw [Measure.deterministic_comp_eq_map]
          rw [Measure.map_map]
          rfl
          all_goals fun_prop
    _ = stepKernel policy ∘ₘ pathMarginal policy current n := by
          rfl

/-- Every single-time marginal of the infinite path law is exactly the
existing bounded PMF executor, converted to a measure. -/
theorem pathLaw_finiteMarginal_eq_stochasticHistoryPMFFrom_toMeasure
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    ∀ n,
      (pathLaw policy current).map (fun path => path n) =
        (A.stochasticHistoryPMFFrom policy current n).toMeasure := by
  intro n
  induction n with
  | zero =>
      rw [← pathMarginal]
      rw [pathMarginal_zero]
      rw [A.stochasticHistoryPMFFrom_zero]
      exact (PMF.toMeasure_pure current).symm
  | succ n ih =>
      rw [← pathMarginal]
      rw [pathMarginal_succ]
      have ihmarginal :
          pathMarginal policy current n =
            (A.stochasticHistoryPMFFrom policy current n).toMeasure :=
        ih
      rw [ihmarginal]
      rw [stepKernel_comp_toMeasure]
      apply congrArg PMF.toMeasure
      calc
        (A.stochasticHistoryPMFFrom policy current n).bind
            (absorbingStepPMF policy) =
          (A.stochasticHistoryPMFFrom policy current n).bind
            (fun middle =>
              A.stochasticHistoryPMFFrom policy middle 1) := by
                apply congrArg
                  ((A.stochasticHistoryPMFFrom
                    policy current n).bind)
                funext middle
                exact
                  absorbingStepPMF_eq_stochasticHistoryPMFFrom_one
                    policy middle
        _ = A.stochasticHistoryPMFFrom policy current (n + 1) :=
          (A.stochasticHistoryPMFFrom_add
            policy current n 1).symm

/-- A transition is legal for the terminal-absorbing history process when it
either stays at a terminal history or appends an action with positive policy
mass at a nonterminal history. -/
def IsLegalAbsorbingTransition
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current next : A.HistoryFrom start) : Prop :=
  (A.IsTerminal current.1 ∧ next = current) ∨
    ∃ hnonterminal : ¬ A.IsTerminal current.1,
      ∃ action ∈ (policy current hnonterminal).support,
        next =
          ⟨A.next current.1 action, current.2.snoc action⟩

theorem stepKernel_ae_legalTransition
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    ∀ᵐ next ∂stepKernel policy current,
      IsLegalAbsorbingTransition policy current next := by
  rw [MeasureTheory.ae_iff_prob_eq_one (measurable_of_countable _)]
  rw [stepKernel_apply]
  rw [(absorbingStepPMF policy current).toMeasure_apply_eq_one_iff
    (Set.to_countable _).measurableSet]
  intro next hnext
  by_cases hterminal : A.IsTerminal current.1
  · left
    refine ⟨hterminal, ?_⟩
    rw [absorbingStepPMF, dif_pos hterminal] at hnext
    exact (PMF.mem_support_pure_iff current next).mp hnext
  · right
    refine ⟨hterminal, ?_⟩
    rw [absorbingStepPMF, dif_neg hterminal] at hnext
    obtain ⟨action, haction, rfl⟩ :=
      (PMF.mem_support_map_iff
        (fun action =>
          (⟨A.next current.1 action,
              current.2.snoc action⟩ :
            A.HistoryFrom start))
        (policy current hterminal) next).mp hnext
    exact ⟨action, haction, rfl⟩

/-- Almost every infinite trajectory follows the terminal-absorbing policy at
every discrete event time. -/
theorem pathLaw_ae_legalTransition
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    ∀ᵐ path ∂pathLaw policy current,
      ∀ n,
        IsLegalAbsorbingTransition policy
          (path n) (path (n + 1)) := by
  rw [eventually_countable_forall]
  intro n
  have hjoint :
      (pathLaw policy current).map (Preorder.frestrictLe n) ⊗ₘ
          trajectoryKernel policy n =
        (pathLaw policy current).map
          (fun path =>
            (Preorder.frestrictLe n path, path (n + 1))) := by
    exact
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ => A.HistoryFrom start)
        (μ₀ := Measure.dirac current)
        (κ := trajectoryKernel policy) (a := n)
  have hcomp :
      ∀ᵐ pair ∂
          ((pathLaw policy current).map
            (Preorder.frestrictLe n) ⊗ₘ
              trajectoryKernel policy n),
        IsLegalAbsorbingTransition policy
          (pair.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) pair.2 := by
    apply Measure.ae_compProd_of_ae_ae
      (Set.to_countable _).measurableSet
    filter_upwards with historyPrefix
    change
      ∀ᵐ next ∂stepKernel policy
          (historyPrefix ⟨n, Finset.mem_Iic.mpr le_rfl⟩),
        IsLegalAbsorbingTransition policy
          (historyPrefix ⟨n, Finset.mem_Iic.mpr le_rfl⟩) next
    exact
      stepKernel_ae_legalTransition policy
        (historyPrefix ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  rw [hjoint] at hcomp
  exact MeasureTheory.ae_of_ae_map (by fun_prop) hcomp

/-- Terminal histories are absorbing almost surely along the infinite path
law. -/
theorem pathLaw_terminal_absorbing
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    ∀ᵐ path ∂pathLaw policy current,
      ∀ n, A.IsTerminal (path n).1 →
        path (n + 1) = path n := by
  filter_upwards [pathLaw_ae_legalTransition policy current]
    with path hlegal
  intro n hterminal
  rcases hlegal n with hstay | hstep
  · exact hstay.2
  · exact False.elim (hstep.1 hterminal)

/-- The coordinate process on the infinite history-path space. -/
def historyCoordinateProcess
    (n : ℕ) (path : ℕ → A.HistoryFrom start) :
    A.HistoryFrom start :=
  path n

/-- The natural filtration generated by finite history coordinates. -/
noncomputable def historyPathFiltration
    [MeasurableSpace (A.HistoryFrom start)]
    [TopologicalSpace (A.HistoryFrom start)]
    [TopologicalSpace.MetrizableSpace (A.HistoryFrom start)]
    [BorelSpace (A.HistoryFrom start)]
    [SecondCountableTopology (A.HistoryFrom start)] :
    MeasureTheory.Filtration ℕ
      (inferInstance :
        MeasurableSpace (ℕ → A.HistoryFrom start)) :=
  MeasureTheory.Filtration.natural
    (historyCoordinateProcess (A := A) (start := start))
    (fun n =>
      (measurable_pi_apply n).stronglyMeasurable)

/-- The set of terminal complete histories. -/
def terminalHistorySet : Set (A.HistoryFrom start) :=
  {history | A.IsTerminal history.1}

/-- First terminal event time, with `⊤` reserved for paths that never
terminate. -/
noncomputable def terminalTime
    (path : ℕ → A.HistoryFrom start) : WithTop ℕ :=
  MeasureTheory.hittingAfter
    (historyCoordinateProcess (A := A) (start := start))
    (terminalHistorySet (A := A) (start := start)) 0 path

/-- The first terminal event time is a stopping time for the natural history
filtration. -/
theorem terminalTime_isStoppingTime
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    [TopologicalSpace (A.HistoryFrom start)]
    [TopologicalSpace.MetrizableSpace (A.HistoryFrom start)]
    [BorelSpace (A.HistoryFrom start)]
    [SecondCountableTopology (A.HistoryFrom start)] :
    MeasureTheory.IsStoppingTime
      (historyPathFiltration (A := A) (start := start))
      (terminalTime (A := A) (start := start)) := by
  apply MeasureTheory.Adapted.isStoppingTime_hittingAfter
  · exact
      (MeasureTheory.Filtration.stronglyAdapted_natural
        (u := historyCoordinateProcess (A := A) (start := start))
        (fun n =>
          (measurable_pi_apply n).stronglyMeasurable)).adapted
  · exact (Set.to_countable _).measurableSet

/-- Almost-sure termination of one terminal-absorbing path law. -/
def AETerminates
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) : Prop :=
  ∀ᵐ path ∂pathLaw policy current,
    terminalTime (A := A) (start := start) path ≠ ⊤

/-- Once a terminal history is reached on an absorbing path, every later
coordinate is the same terminal history. -/
theorem path_eq_of_terminal_of_le
    (path : ℕ → A.HistoryFrom start)
    (habsorbing :
      ∀ n, A.IsTerminal (path n).1 →
        path (n + 1) = path n)
    {first later : ℕ}
    (hterminal : A.IsTerminal (path first).1)
    (hle : first ≤ later) :
    path later = path first ∧ A.IsTerminal (path later).1 := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction steps with
  | zero =>
      simpa
  | succ steps ih =>
      have ih' :=
        ih (Nat.le_add_right first steps)
      have hstep :
          path (first + steps + 1) =
            path (first + steps) :=
        habsorbing (first + steps) ih'.2
      constructor
      · rw [Nat.add_succ]
        exact hstep.trans ih'.1
      · rw [Nat.add_succ, hstep]
        exact ih'.2

/-- Bounded terminal payoff: nonterminal horizon exhaustion is assigned the
explicit value `0`, without reading the game's nonterminal payoff filler. -/
def stoppedPayoff
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (payoff : A.HistoryFrom start → ℝ)
    (n : ℕ) (path : ℕ → A.HistoryFrom start) : ℝ :=
  if A.IsTerminal (path n).1 then payoff (path n) else 0

/-- Infinite-execution terminal payoff, with explicit value `0` on paths that
never terminate. -/
noncomputable def terminalPayoff
    (payoff : A.HistoryFrom start → ℝ)
    (path : ℕ → A.HistoryFrom start) : ℝ :=
  if htop :
      terminalTime (A := A) (start := start) path = ⊤ then
    0
  else
    payoff
      (path
        ((terminalTime (A := A) (start := start) path).untop htop))

/-- On a terminal-absorbing path that terminates, bounded stopped payoffs
eventually equal the infinite terminal payoff. -/
theorem stoppedPayoff_tendsto_of_path
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (payoff : A.HistoryFrom start → ℝ)
    (path : ℕ → A.HistoryFrom start)
    (habsorbing :
      ∀ n, A.IsTerminal (path n).1 →
        path (n + 1) = path n)
    (hterminates :
      terminalTime (A := A) (start := start) path ≠ ⊤) :
    Filter.Tendsto
      (fun n => stoppedPayoff payoff n path)
      Filter.atTop
      (nhds (terminalPayoff payoff path)) := by
  let hit :=
    (terminalTime (A := A) (start := start) path).untop
      hterminates
  have hhit :
      A.IsTerminal (path hit).1 := by
    have hmem :=
      MeasureTheory.hittingAfter_mem_set_of_ne_top
        (u := historyCoordinateProcess (A := A) (start := start))
        (s := terminalHistorySet (A := A) (start := start))
        (n := 0) (ω := path) hterminates
    change A.IsTerminal
      (path
        (terminalTime (A := A) (start := start) path).untopA).1 at hmem
    rw [WithTop.untopA_eq_untop hterminates] at hmem
    exact hmem
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventually_atTop.2 ⟨hit, ?_⟩
  intro n hn
  have hstable :=
    path_eq_of_terminal_of_le path habsorbing hhit hn
  change
    terminalPayoff payoff path =
      (if A.IsTerminal (path n).1 then
        payoff (path n) else 0)
  rw [if_pos hstable.2]
  rw [terminalPayoff, dif_neg hterminates]
  exact congrArg payoff hstable.1 |>.symm

/-- Under almost-sure termination, bounded stopped payoffs converge almost
everywhere to the infinite terminal payoff. -/
theorem stoppedPayoff_tendsto_ae
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (payoff : A.HistoryFrom start → ℝ)
    (hterminates : AETerminates policy current) :
    ∀ᵐ path ∂pathLaw policy current,
      Filter.Tendsto
        (fun n => stoppedPayoff payoff n path)
        Filter.atTop
        (nhds (terminalPayoff payoff path)) := by
  filter_upwards
    [pathLaw_terminal_absorbing policy current, hterminates]
    with path habsorbing hfinite
  exact
    stoppedPayoff_tendsto_of_path payoff path
      habsorbing hfinite

/-- Every bounded stopped-payoff functional is measurable when the payoff on
terminal histories is measurable. -/
theorem stoppedPayoff_measurable
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (payoff : A.HistoryFrom start → ℝ)
    (hpayoff : Measurable payoff)
    (n : ℕ) :
    Measurable (stoppedPayoff payoff n) := by
  apply Measurable.ite
  · exact
      (Set.to_countable
        (terminalHistorySet (A := A) (start := start))).measurableSet.preimage
        (measurable_pi_apply n)
  · exact hpayoff.comp (measurable_pi_apply n)
  · exact measurable_const

/-- Dominated convergence for expected terminal payoff. The hypotheses expose
the measurable payoff, an integrable dominating function, its pointwise
domination, and almost-sure termination explicitly. -/
theorem expectedStoppedPayoff_tendsto_of_dominated
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (payoff : A.HistoryFrom start → ℝ)
    (hpayoff : Measurable payoff)
    (bound : (ℕ → A.HistoryFrom start) → ℝ)
    (hbound :
      ∀ n, ∀ᵐ path ∂pathLaw policy current,
        ‖stoppedPayoff payoff n path‖ ≤ bound path)
    (hbound_integrable :
      MeasureTheory.Integrable bound (pathLaw policy current))
    (hterminates : AETerminates policy current) :
    Filter.Tendsto
      (fun n =>
        ∫ path, stoppedPayoff payoff n path
          ∂pathLaw policy current)
      Filter.atTop
      (nhds
        (∫ path, terminalPayoff payoff path
          ∂pathLaw policy current)) := by
  exact
    MeasureTheory.tendsto_integral_of_dominated_convergence
      bound
      (fun n =>
        (stoppedPayoff_measurable payoff hpayoff n
          ).aestronglyMeasurable)
      hbound_integrable hbound
      (stoppedPayoff_tendsto_ae
        policy current payoff hterminates)

/-- Paths unfinished at event time `n`. -/
def unfinishedAt (n : ℕ) :
    Set (ℕ → A.HistoryFrom start) :=
  {path | ¬ A.IsTerminal (path n).1}

/-- Probability mass of paths that remain nonterminal at event time `n`. -/
noncomputable def noneMass
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (n : ℕ) : ℝ≥0∞ :=
  pathLaw policy current
    (unfinishedAt (A := A) (start := start) n)

theorem unfinishedAt_measurableSet
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (n : ℕ) :
    MeasurableSet
      (unfinishedAt (A := A) (start := start) n) :=
  ((Set.to_countable
    (terminalHistorySet (A := A) (start := start))).measurableSet.preimage
      (measurable_pi_apply n)).compl

/-- Under almost-sure termination, the unfinished/`none` mass tends to zero. -/
theorem noneMass_tendsto_zero_of_aeTerminates
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (hterminates : AETerminates policy current) :
    Filter.Tendsto
      (noneMass policy current)
      Filter.atTop (nhds 0) := by
  have hlim :
      ∀ᵐ path ∂pathLaw policy current,
        ∀ᶠ n in Filter.atTop,
          path ∈ unfinishedAt (A := A) (start := start) n ↔
            path ∈ (∅ : Set (ℕ → A.HistoryFrom start)) := by
    filter_upwards
      [pathLaw_terminal_absorbing policy current, hterminates]
      with path habsorbing hfinite
    let hit :=
      (terminalTime (A := A) (start := start) path).untop
        hfinite
    have hhit :
        A.IsTerminal (path hit).1 := by
      have hmem :=
        MeasureTheory.hittingAfter_mem_set_of_ne_top
          (u := historyCoordinateProcess (A := A) (start := start))
          (s := terminalHistorySet (A := A) (start := start))
          (n := 0) (ω := path) hfinite
      change A.IsTerminal
        (path
          (terminalTime (A := A) (start := start) path).untopA).1 at hmem
      rw [WithTop.untopA_eq_untop hfinite] at hmem
      exact hmem
    refine Filter.eventually_atTop.2 ⟨hit, ?_⟩
    intro n hn
    have hstable :=
      path_eq_of_terminal_of_le path habsorbing hhit hn
    simp [unfinishedAt, hstable.2]
  have hmeasure :=
    MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      Filter.atTop
      (μ := pathLaw policy current)
      (A := (∅ : Set (ℕ → A.HistoryFrom start)))
      MeasurableSet.empty
      (fun n =>
        unfinishedAt_measurableSet
          (A := A) (start := start) n)
      hlim
  simpa [noneMass] using hmeasure

/-- The infinite path law packaged as a probability measure. -/
noncomputable def pathProbabilityMeasure
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    MeasureTheory.ProbabilityMeasure
      (ℕ → A.HistoryFrom start) :=
  ⟨pathLaw policy current, inferInstance⟩

/-- The terminal payoff is almost-everywhere measurable under an
almost-surely terminating path law. -/
theorem terminalPayoff_aemeasurable
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (payoff : A.HistoryFrom start → ℝ)
    (hpayoff : Measurable payoff)
    (hterminates : AETerminates policy current) :
    AEMeasurable (terminalPayoff payoff)
      (pathLaw policy current) := by
  exact
    (aestronglyMeasurable_of_tendsto_ae
      Filter.atTop
      (fun n =>
        (stoppedPayoff_measurable payoff hpayoff n
          ).aestronglyMeasurable)
      (stoppedPayoff_tendsto_ae
        policy current payoff hterminates)).aemeasurable

/-- Law of the bounded stopped payoff at event time `n`. -/
noncomputable def stoppedPayoffLaw
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (payoff : A.HistoryFrom start → ℝ)
    (hpayoff : Measurable payoff)
    (n : ℕ) :
    MeasureTheory.ProbabilityMeasure ℝ :=
  (pathProbabilityMeasure policy current).map
    (stoppedPayoff_measurable payoff hpayoff n).aemeasurable

/-- Law of the infinite terminal payoff. -/
noncomputable def terminalPayoffLaw
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (payoff : A.HistoryFrom start → ℝ)
    (hpayoff : Measurable payoff)
    (hterminates : AETerminates policy current) :
    MeasureTheory.ProbabilityMeasure ℝ :=
  (pathProbabilityMeasure policy current).map
    (terminalPayoff_aemeasurable
      policy current payoff hpayoff hterminates)

/-- Weak convergence of bounded stopped-payoff laws to the terminal-payoff
law under almost-sure termination. -/
theorem stoppedPayoffLaw_tendsto_terminalPayoffLaw
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (payoff : A.HistoryFrom start → ℝ)
    (hpayoff : Measurable payoff)
    (hterminates : AETerminates policy current) :
    Filter.Tendsto
      (fun n => stoppedPayoffLaw
        policy current payoff hpayoff n)
      Filter.atTop
      (nhds
        (terminalPayoffLaw
          policy current payoff hpayoff hterminates)) := by
  rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hterminal :
      AEStronglyMeasurable
        (terminalPayoff payoff)
        (pathLaw policy current) :=
    (aestronglyMeasurable_of_tendsto_ae
      Filter.atTop
      (fun n =>
        (stoppedPayoff_measurable payoff hpayoff n
          ).aestronglyMeasurable)
      (stoppedPayoff_tendsto_ae
        policy current payoff hterminates))
  have hterminalMeasurable :
      AEStronglyMeasurable f
        ((pathLaw policy current).map
          (terminalPayoff payoff)) :=
    f.continuous.aestronglyMeasurable
  have hconvergence :
      Filter.Tendsto
        (fun n =>
          ∫ path, f (stoppedPayoff payoff n path)
            ∂pathLaw policy current)
        Filter.atTop
        (nhds
          (∫ path, f (terminalPayoff payoff path)
            ∂pathLaw policy current)) := by
    apply
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ => ‖f‖)
    · intro n
      exact
        f.continuous.aestronglyMeasurable.comp_aemeasurable
          (stoppedPayoff_measurable
            payoff hpayoff n).aemeasurable
    · exact MeasureTheory.integrable_const ‖f‖
    · intro n
      filter_upwards with path
      exact f.norm_coe_le_norm _
    · filter_upwards
        [stoppedPayoff_tendsto_ae
          policy current payoff hterminates]
        with path hpath
      exact f.continuous.continuousAt.tendsto.comp hpath
  convert hconvergence using 1
  · funext n
    exact MeasureTheory.integral_map
      (stoppedPayoff_measurable
        payoff hpayoff n).aemeasurable
      f.continuous.aestronglyMeasurable
  · exact congrArg nhds <|
      MeasureTheory.integral_map
        (terminalPayoff_aemeasurable
          policy current payoff hpayoff hterminates)
        hterminalMeasurable

end Arena
