/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Discrete
import EconCSLib.GameTheory.ExtensiveGame.Observed.FiniteUnfolding
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
law, while `completeInformation` composes that law with the core
complete-history presentation and an explicit root selection.
`FiniteEFGHypotheses.toFiniteHistoryGame` extracts a finite,
occurrence-sensitive reachable-history carrier without requiring
`Fintype State`. The payoff-free discrete chance layer exposes exact bounded
complete-history PMFs while keeping full infinite path measures out of this
facade.

Measure-valued infinite discrete paths are available from
`Interface.Execution.Infinite`; the former combined
`Interface.Execution.Discrete` path was deleted before API stability.
-/
