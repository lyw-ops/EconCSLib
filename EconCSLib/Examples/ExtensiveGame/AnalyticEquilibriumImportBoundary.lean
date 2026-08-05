/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic

/-!
# Analytic equilibrium import boundary

The analytic equilibrium layer reuses the discrete equilibrium surface and
adds arbitrary-measure pure-strategy laws, measurable-kernel path utility, and
continuation semantics, while Restart and Compilation remain independent
branches.
-/

#check ExtensiveGame.ObservedChanceGame.finiteKuhn_isNash_iff
#check ExtensiveGame.ObservedGame.PureProfileMeasurableModel
#check ExtensiveGame.ObservedGame.ArbitraryMeasurePureStrategy
#check ExtensiveGame.ObservedGame.ArbitraryMeasurePureProfileLaw
#check ExtensiveGame.ObservedGame.ArbitraryMeasurePureProfileLaw.outcomeLaw_ofPMF
#check ExtensiveGame.ObservedGame.MeasurableHistoryModel.PathUtility
#check ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedPathUtility.IsNashOnPresentation

/--
error: Unknown constant `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStateCompatibleAt`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStateCompatibleAt

/--
error: Unknown identifier `GameTree.Kuhn_exists_occurrencePureSPE`
-/
#guard_msgs in
#check GameTree.Kuhn_exists_occurrencePureSPE
