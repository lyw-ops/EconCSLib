/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Relations.Discrete
import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Continuation
import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorMorphism
import EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Termination
import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Execution
import EconCSLib.GameTheory.ExtensiveGame.Observed.MorphismHierarchy
import EconCSLib.GameTheory.ExtensiveGame.Observed.SPE
import EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall
import EconCSLib.GameTheory.ExtensiveGame.Observed.Realization
import EconCSLib.GameTheory.ExtensiveGame.Observed.Mixed
import EconCSLib.GameTheory.ExtensiveGame.Observed.Continuation
import EconCSLib.GameTheory.ExtensiveGame.Observed.Kuhn
import EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Realization
import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Realization
import EconCSLib.GameTheory.ExtensiveGame.Observed.StrategyBridge

/-!
# Discrete EFG equilibrium

Stable public import for pure, behavioral, and mixed finite-fuel equilibrium
semantics and their structural representation-transfer theorems.

It extends `Interface.Relations.Discrete` with bounded and
termination-certified equilibrium predicates, subgame perfection on lawful
systems, perfect recall, PMF realization, finite Kuhn bridges, conditioning,
and the uniform strategy bridge. It does not import infinite path measures,
non-atomic measurable kernels, measurable path utilities, continuation
conditioning, fresh-clock restart, or concrete compilers.
-/
