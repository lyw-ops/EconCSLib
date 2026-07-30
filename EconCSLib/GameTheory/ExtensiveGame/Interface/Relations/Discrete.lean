/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite
import EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.Morphism
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.KernelWeakSimulation
import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Operational
import EconCSLib.GameTheory.ExtensiveGame.Observed.Chance
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior
import EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Structural
import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Structural

/-!
# Discrete and structural EFG relations

Stable public import for strict structural representation changes,
information refinements, PMF-kernel trajectory couplings, and
weak/stuttering simulations.

It extends `Interface.Execution.Finite` and deliberately excludes
measure-valued infinite paths and the `MeasurableKernelArena` implementation
stack. Continuation/Nash transfer belongs to `Interface.Equilibrium.Discrete`;
analytic execution remains available through the compatibility aggregate
`Interface.Relations` or directly through `Interface.Execution.Analytic`.
-/
