/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete

/-!
# Discrete equilibrium import boundary

Finite-fuel pure, behavioral, mixed, and Kuhn equilibrium semantics remain
available without the measure-valued execution and path-utility layers.
-/

#check ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff
#check ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff
#check ExtensiveGame.ObservedChanceGame.finiteKuhn_isNash_iff
#check ExtensiveGame.ObservedGame.DiscreteGeneralStrategy
#check ExtensiveGame.ObservedGame.DiscreteGeneralProfile.behavioralProfileLaw
#check ExtensiveGame.ObservedChanceGame.BoundedCompleteHistorySemantics
#check ExtensiveGame.ObservedChanceGame.BoundedCompleteHistorySemantics.CompleteHistoryLawRealization
#check ExtensiveGame.ControlledObservedGame.ContinuationSemantics
#check ExtensiveGame.ControlledObservedGame.ContinuationSemantics.IsEvaluatorContinuationEquilibriumAt
#check ExtensiveGame.ControlledObservedGame.ContinuationSemantics.isEvaluatorContinuationEquilibriumAt_iff_of_surjective
#check ExtensiveGame.ObservedGame.ofControlledObservedGame
#check ExtensiveGame.ObservedGame.relabelPlayers
#check ExtensiveGame.ObservedGame.relabelPureProfileEquiv
#check ExtensiveGame.ObservedGame.ContinuationSemantics

/--
error: Unknown constant `ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff_viaContinuationFamily`
-/
#guard_msgs in
#check
  ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff_viaContinuationFamily

/--
error: Unknown constant `ExtensiveGame.ObservedGame.InformationRefinement.isPureNashOnRootsAtFuel_of_map_viaContinuationSimulation`
-/
#guard_msgs in
#check
  ExtensiveGame.ObservedGame.InformationRefinement.isPureNashOnRootsAtFuel_of_map_viaContinuationSimulation

/--
error: Unknown constant `ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff_viaInformationRefinement`
-/
#guard_msgs in
#check
  ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff_viaInformationRefinement

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

/--
error: Unknown constant `ExtensiveGame.ObservedGame.MeasurableHistoryModel.PathUtility`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.MeasurableHistoryModel.PathUtility
