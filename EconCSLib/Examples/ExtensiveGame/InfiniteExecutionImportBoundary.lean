/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite

/-!
# Infinite discrete execution import boundary

Infinite PMF-driven paths intentionally introduce Mathlib kernels and measures
while remaining independent of the non-atomic `MeasurableKernelArena` stack.
-/

#check Arena.stochasticHistoryPMFFrom
#check Arena.pathLaw
#check ProbabilityTheory.Kernel

/--
error: Unknown identifier `MeasurableKernelArena`
-/
#guard_msgs in
#check MeasurableKernelArena
