/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite

/-!
# Discrete infinite-path EFG execution

Compatibility aggregate for finite PMF execution and measure-valued infinite
natural-number-indexed event paths.

New finite-horizon clients should import `Interface.Execution.Finite`, which
does not import Mathlib Markov kernels or measure-valued path semantics. This
legacy path additionally supplies terminal-absorbing infinite trajectory
laws, almost-sure termination and payoff convergence, and observed behavioral
specialization through `Interface.Execution.Infinite`. It still excludes the
non-atomic `MeasurableKernelArena` execution stack, equilibrium transfer, and
concrete compilers.
-/
