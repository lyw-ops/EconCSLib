/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelArena

/-!
# Finite-horizon discrete EFG execution

Stable public import for deterministic and PMF-valued execution with finite
fuel.

This tier adds observed behavioral/chance execution and the discrete
`KernelArena` without importing infinite path measures, Mathlib Markov
kernels, non-atomic measurable-kernel execution, equilibrium transfer, or
concrete compilers. It is the recommended execution entry for finite games
and for clients whose stochastic semantics remain PMF-valued.
`ObservedChanceGame.withChanceKernel` attaches an explicit normalized chance
law, while `completeInformationPresentation` composes that law with the core
complete-history presentation and an explicit root selection.

Measure-valued infinite discrete paths are available from
`Interface.Execution.Infinite`; the older `Interface.Execution.Discrete`
import remains a compatibility alias for their union with this tier.
-/
