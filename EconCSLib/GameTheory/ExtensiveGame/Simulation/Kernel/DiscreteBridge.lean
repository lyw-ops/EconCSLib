/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.StatePath
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.KernelBridge

/-!
# Kernel.DiscreteBridge — exact discrete-to-analytic infinite-path bridge

This module identifies the discrete complete-history path law with the
canonical measurable-kernel path law after lifting complete histories to
states and applying the discrete-to-analytic kernel embedding.

The result is equality of the complete probability measures on infinite
paths, not only equality of their one-coordinate marginals. It closes the
coherence boundary between `Arena.pathLaw` and
`MeasurableKernelArena.ActionPolicy.pathMeasure`.
-/

open MeasureTheory ProbabilityTheory

namespace Arena

variable {A : Arena} {start : A.State}

noncomputable section

local instance historyMeasurableSpace :
    MeasurableSpace (A.HistoryFrom start) :=
  ⊤

/-- The discrete history step kernel is exactly the stopped analytic step
kernel of the lifted history arena. -/
theorem stepKernel_eq_historyKernelArena_toMeasurable
    [(state : A.State) → Decidable (A.IsTerminal state)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) :
    Arena.stepKernel policy =
      policy.toKernelPolicy.toMeasurable.stepKernel
        (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet := by
  apply Kernel.ext
  intro current
  by_cases hterminal : A.IsTerminal current.1
  · rw [Arena.stepKernel_apply, Arena.absorbingStepPMF,
      dif_pos hterminal]
    simpa only [PMF.toMeasure_pure] using
      (KernelArena.Policy.toMeasurable_stepKernel_apply_terminal
        policy.toKernelPolicy current hterminal).symm
  · rw [Arena.stepKernel_apply, Arena.absorbingStepPMF,
      dif_neg hterminal]
    simpa only [Arena.historyKernelArena_stepLaw] using
      (KernelArena.Policy.toMeasurable_stepKernel_apply_nonterminal
        policy.toKernelPolicy current hterminal).symm

/-- The two Ionescu--Tulcea constructions use exactly the same finite-history
transition kernels after the complete-history state lift. -/
theorem trajectoryKernel_eq_historyKernelArena_toMeasurable
    [(state : A.State) → Decidable (A.IsTerminal state)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start) :
    Arena.trajectoryKernel policy =
      policy.toKernelPolicy.toMeasurable.pathStepKernel
        (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet := by
  funext time
  rw [Arena.trajectoryKernel,
    MeasurableKernelArena.ActionPolicy.pathStepKernel]
  rw [Arena.stepKernel_eq_historyKernelArena_toMeasurable policy]
  rfl

/-- The discrete terminal-absorbing complete-history path law is exactly the
analytic path measure of the embedded lifted history policy.

This is full path-measure equality. Consequently every measurable path event,
finite prefix, stopping event, and measurable path functional has the same law
in the two presentations. -/
theorem pathLaw_eq_historyKernelArena_toMeasurable_pathMeasure
    [(state : A.State) → Decidable (A.IsTerminal state)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    Arena.pathLaw policy current =
      policy.toKernelPolicy.toMeasurable.pathMeasure
        (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet
        current := by
  rw [Arena.pathLaw]
  rw [
    MeasurableKernelArena.ActionPolicy.pathMeasure_eq_trajMeasure]
  have hkernel :=
    Arena.trajectoryKernel_eq_historyKernelArena_toMeasurable policy
  simp only [hkernel]
  congr

end

end Arena
