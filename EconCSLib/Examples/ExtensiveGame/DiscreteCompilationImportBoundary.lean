/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete

/-!
# Discrete compilation import boundary

The finite reference compilers and PMF-valued FOSG serialization reuse
discrete equilibrium without importing measurable-kernel execution.
-/

#check GameTree.Kuhn_exists_occurrencePureSPE
#check ExtensiveGame.ObservedChanceGame.finiteKuhn_isNash_iff
#check StochasticGameTree.toObservedChanceGame
#check StochasticGameTree.stochasticHistoryPMFFrom_map_payoff
#check FiniteImperfectGame.ObservedChanceCompiler.toObservedChanceGame
#check ExtensiveGame.FOSG.Sequentialization.observedChanceGameCore
#check ExtensiveGame.FOSG.Sequentialization.observedChanceGame
#check ExtensiveGame.FOSG.Sequentialization.observedChanceGame_eq_core
#check ExtensiveGame.FOSG.Sequentialization.rootPresentation

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
