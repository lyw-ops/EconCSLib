/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledInfrastructure
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledInfrastructureCompat
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledMorphism
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledMorphismCompat
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledDiscreteLawCompat
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledDiscretePathLaw
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledAnalyticLaw
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledSemantics
import EconCSLib.GameTheory.ExtensiveGame.Observed.Semantics

/-!
# Controlled compatibility import boundaries

The two established aggregate paths continue to re-export declarations from
their responsibility leaves after becoming import-only compatibility modules.
The complete flat `Controlled*` family and the state-payoff semantics frontend
also elaborate together: canonical controlled names and payoff-aware adapter
names remain in disjoint namespaces.
-/

#check ExtensiveGame.ControlledObservedGame
#check ExtensiveGame.ControlledObservedGame.FiniteEFGHypotheses
#check ExtensiveGame.ControlledObservedGame.RecallCertificate
#check ExtensiveGame.ControlledObservedGame.SubgameSystem
#check ExtensiveGame.ControlledObservedGame.Iso
#check ExtensiveGame.ControlledObservedGame.Iso.mapSubgameSystem
#check ExtensiveGame.ControlledObservedGame.Iso.perfectRecall_iff
#check ExtensiveGame.ControlledObservedGame.ContinuationSemantics
#check ExtensiveGame.ControlledObservedGame.CompletePathLawSemantics
#check ExtensiveGame.DiscreteControlledObservedChanceGame
#check ExtensiveGame.ObservedGame.ContinuationSemantics
#check ExtensiveGame.ObservedGame.PayoffCompatibleIso
#check ExtensiveGame.ObservedGame.pureStrategy_toControlled
#check ExtensiveGame.ObservedChanceGame.toDiscreteControlledObservedChanceGame
