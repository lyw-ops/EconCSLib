/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Chance
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledDiscreteLaw

/-!
# Payoff-aware adapter for discrete controlled chance

This module forgets only the payoff interpretation of an
`ObservedChanceGame`.  Discrete chance and bounded execution remain owned by
the payoff-free `ControlledDiscreteLaw` module.
-/

namespace ExtensiveGame.ObservedChanceGame

variable {N U : Type*}

/-- Forget payoffs from a discrete observed chance game while retaining its
complete history and chance laws definitionally. -/
def toDiscreteControlledObservedChanceGame
    (G : ObservedChanceGame N U) :
    DiscreteControlledObservedChanceGame N where
  observed := G.observed.toControlledObservedGame
  chanceKernel := G.chanceKernel

end ExtensiveGame.ObservedChanceGame
