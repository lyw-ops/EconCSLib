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

/--
error: Unknown constant `ExtensiveGame.ObservedGame.Iso.isPureNashOnDesignatedContinuationsAtFuel_iff`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.Iso.isPureNashOnDesignatedContinuationsAtFuel_iff

/--
error: Unknown constant `ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnDesignatedContinuationsAtFuel_iff`
-/
#guard_msgs in
#check ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnDesignatedContinuationsAtFuel_iff
