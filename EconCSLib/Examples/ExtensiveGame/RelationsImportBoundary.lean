/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Relations

/-!
# Relations/equilibrium import boundary

The historical relations aggregate exposes structural representation changes,
operational simulation relations, and analytic execution. Bounded Nash,
termination, and equilibrium transfer remain owned by
`Interface.Equilibrium`; measure-free relation clients use
`Interface.Relations.Discrete`.
-/

#check ExtensiveGame.ObservedGame.InformationRefinement
#check Arena.WeakSimulation
#check MeasurableKernelArena
#check ExtensiveGame.ObservedChanceGame.CompletePathLawSemantics
#check ExtensiveGame.ObservedChanceGame.CompletePathLawSemantics.CompletePathLawRealization
#check ExtensiveGame.Preservation.StructuralHom
#check ExtensiveGame.Preservation.StrictIso
#check ExtensiveGame.Preservation.PayoffCompatibleIso
#check ExtensiveGame.Preservation.InformationRefinement
#check ExtensiveGame.Preservation.Simulation
#check ExtensiveGame.Preservation.Bisimulation
#check ExtensiveGame.Preservation.WeakSimulation
#check ExtensiveGame.Preservation.WeakBisimulation
#check ExtensiveGame.Preservation.CompleteHistoryLawRealization
#check ExtensiveGame.Preservation.CompletePathLawRealization
#check ExtensiveGame.Preservation.PathLawCoupling
#check ExtensiveGame.Preservation.StrictCompilerPreservation
#check ExtensiveGame.Preservation.WeakCompilerPreservation

/--
error: Unknown constant `ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff

/--
error: Unknown constant `ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff`
-/
#guard_msgs in
#check ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff
