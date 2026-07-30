/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Core

/-!
# Core/discrete import boundary

The core facade provides typed deterministic and stochastic history execution
plus observed-game semantics. Infinite event-time execution and discrete
kernel arenas remain opt-in through `Interface.Execution.Discrete`.
-/

#check ExtensiveGame.ObservedGame
#check ExtensiveGame.ofArena
#check ExtensiveGame.ObservedGame.historyInformationPresentation
#check ExtensiveGame.ObservedGame.completeInformationPresentation
#check ExtensiveGame.ObservedGame.CompleteInformation.PublicObservationPresentation.trivial
#check ExtensiveGame.ObservedGame.ContinuationRootPresentation.initialOnly
#check ExtensiveGame.ObservedGame.ContinuationRootPresentation.allHistories
#check ExtensiveGame.ObservedGame.SubgameSystem.initialOnly
#check Arena.StochasticHistoryPolicy

/--
error: Unknown identifier `KernelArena`
-/
#guard_msgs in
#check KernelArena

/--
error: Unknown constant `Arena.pathLaw`
-/
#guard_msgs in
#check Arena.pathLaw

/--
error: Unknown constant `ExtensiveGame.ObservedChanceGame.withChanceKernel`
-/
#guard_msgs in
#check ExtensiveGame.ObservedChanceGame.withChanceKernel

namespace CompleteInformationInstanceBoundary

open ExtensiveGame

variable {N U : Type*} (base : ExtensiveGame N U)
  (roots : ObservedGame.ContinuationRootPresentation base) (i : N)

abbrev observed :=
  ObservedGame.completeInformationPresentation base roots

/-- Decidable equality on histories is reused without a constructor-specific
typeclass assumption. -/
example [DecidableEq (base.toArena.HistoryFrom base.init)] :
    DecidableEq ((observed base roots).Observation i) :=
  inferInstance

/-- Finiteness on histories is likewise inherited definitionally by
observations and information states. -/
example [Fintype (base.toArena.HistoryFrom base.init)] :
    Fintype ((observed base roots).InfoState i) :=
  inferInstance

end CompleteInformationInstanceBoundary
