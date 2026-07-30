/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation

/-!
# Compilation/restart import boundary

The historical compilation aggregate combines reference compilers and FOSG
serialization with analytic equilibrium. Measure-free compiler clients use
`Interface.Compilation.Discrete`. Fresh-clock restart compatibility remains
independently opt-in through `Interface.Restart`; this guard prevents the
restart proof stack from leaking into either compiler entry.
-/

#check GameTree.Kuhn_exists_occurrencePureSPE
#check ExtensiveGame.ObservedGame.MeasurableHistoryModel.PathUtility

/--
error: Unknown constant `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStateCompatibleAt`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStateCompatibleAt
