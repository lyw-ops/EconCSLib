/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite

/-!
# Finite PMF execution import boundary

The finite-fuel public entry exposes deterministic, observed behavioral, and
PMF-kernel execution without the measure-valued infinite-path or non-atomic
kernel layers.
-/

#check Arena.stochasticHistoryPMFFrom
#check ExtensiveGame.ObservedChanceGame.withChanceKernel
#check ExtensiveGame.DiscreteObservedChanceGame
#check ExtensiveGame.ObservedChanceGame.completeInformation
#check ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
#check ExtensiveGame.ObservedGame.FiniteEFGHypotheses.toFiniteHistoryGame
#check ExtensiveGame.ObservedGame.FiniteEFGHypotheses.toFiniteObservedGame
#check ExtensiveGame.ObservedGame.FiniteEFGHypotheses.toFiniteObservedChanceGame
#check ExtensiveGame.DiscreteControlledObservedChanceGame.BoundedCompleteHistoryLawSemantics
#check ExtensiveGame.DiscreteControlledObservedChanceGame.BoundedCompleteHistoryLawSemantics.CompleteHistoryLawRealization
#check KernelArena

/--
error: Unknown constant `Arena.pathLaw`
-/
#guard_msgs in
#check Arena.pathLaw

/--
error: Unknown identifier `MeasurableKernelArena`
-/
#guard_msgs in
#check MeasurableKernelArena

/--
error: Unknown identifier `ProbabilityTheory.Kernel`
-/
#guard_msgs in
#check ProbabilityTheory.Kernel
