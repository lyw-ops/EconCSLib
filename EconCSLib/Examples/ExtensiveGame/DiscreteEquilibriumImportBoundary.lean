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

#check ExtensiveGame.ObservedGame.Iso.isPureNashOnDesignatedContinuationsAtFuel_iff
#check ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnDesignatedContinuationsAtFuel_iff
#check ExtensiveGame.ObservedChanceGame.finiteKuhn_isNash_iff

/--
error: Unknown constant `ExtensiveGame.ObservedGame.Iso.isPureNashOnDesignatedContinuationsAtFuel_iff_viaContinuationFamily`
-/
#guard_msgs in
#check
  ExtensiveGame.ObservedGame.Iso.isPureNashOnDesignatedContinuationsAtFuel_iff_viaContinuationFamily

/--
error: Unknown constant `ExtensiveGame.ObservedGame.InformationRefinement.isPureNashOnDesignatedContinuationsAtFuel_of_map_viaContinuationSimulation`
-/
#guard_msgs in
#check
  ExtensiveGame.ObservedGame.InformationRefinement.isPureNashOnDesignatedContinuationsAtFuel_of_map_viaContinuationSimulation

/--
error: Unknown constant `ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnDesignatedContinuationsAtFuel_iff_viaInformationRefinement`
-/
#guard_msgs in
#check
  ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnDesignatedContinuationsAtFuel_iff_viaInformationRefinement

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
