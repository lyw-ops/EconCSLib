/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium

/-!
# Equilibrium/restart import boundary

The historical equilibrium aggregate combines discrete equilibrium and
absolute-prefix analytic continuation equilibrium. Fresh-clock restart
compatibility is intentionally opt-in through `Interface.Restart`, while
compilers are opt-in through `Interface.Compilation`. These negative
compilation guards prevent either branch from leaking back into ordinary
equilibrium imports.
-/

#check ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff
#check ExtensiveGame.ObservedChanceGame.finiteKuhn_isNash_iff
#check ExtensiveGame.ObservedGame.MeasurableHistoryModel.PathUtility

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
