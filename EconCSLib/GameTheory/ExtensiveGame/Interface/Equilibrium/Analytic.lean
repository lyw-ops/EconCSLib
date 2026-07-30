/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete
import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.Outcome
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Observed
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.ObservedConditioning

/-!
# Analytic EFG equilibrium

Stable public import for measurable-kernel path utility, constructive
equilibrium, absolute-prefix continuation, and conditional continuation
semantics.

This layer reuses the complete finite-fuel pure/PMF equilibrium surface from
`Interface.Equilibrium.Discrete` and the analytic execution surface from
`Interface.Execution.Analytic`. Fresh-clock restart and concrete compilation
remain independent higher branches.
-/
