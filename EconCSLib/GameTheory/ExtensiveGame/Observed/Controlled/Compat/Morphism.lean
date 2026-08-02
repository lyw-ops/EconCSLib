/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Inverse

/-!
# Payoff-aware adapters for controlled observed-game morphisms

API role: **downstream payoff-aware adapter**. Despite the shared
`Controlled*` filename prefix, this is not a payoff-free declaration owner
and canonical controlled modules must never import it.

The strict structural relation is owned by `ControlledMorphism`.  This module
adds only the terminal-payoff square and conversion from the legacy
`ObservedGame.Iso`.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*}

/-- A payoff-compatible strict isomorphism is a payoff-free structural
isomorphism plus the terminal-payoff commuting square. -/
structure PayoffCompatibleIso
    (G H : ObservedGame N U) where
  /-- Underlying payoff-free strict isomorphism. -/
  structural :
    G.toControlledObservedGame.Iso
      H.toControlledObservedGame
  /-- Terminal payoff vectors agree at corresponding histories. -/
  map_payoff :
    ∀ history : G.base.toArena.HistoryFrom G.base.init,
      G.base.isTerminal history.1 →
      H.base.payoff
          (structural.historyIso.stateEquiv history).1 =
        G.base.payoff history.1

namespace Iso

variable {G H : ObservedGame N U}

/-- Forget payoff compatibility from the legacy strict observed-game
isomorphism. -/
def toControlledIso (e : G.Iso H) :
    G.toControlledObservedGame.Iso
      H.toControlledObservedGame where
  historyIso := e.historyIso
  map_init := e.map_init
  map_mover := e.map_mover
  observationEquiv := e.observationEquiv
  map_observe := e.map_observe
  publicEquiv := e.publicEquiv
  map_publicObserve := e.map_publicObserve
  map_publicOf := e.map_publicOf
  infoStateEquiv := e.infoStateEquiv
  map_infoObserve := e.map_infoObserve
  infoActionEquiv := e.infoActionEquiv
  map_infoAt := e.map_infoAt
  map_infoActionAt := e.map_infoActionAt

/-- Repackage the legacy strict isomorphism as a structural isomorphism plus
orthogonal payoff compatibility. -/
def toPayoffCompatibleIso (e : G.Iso H) :
    G.PayoffCompatibleIso H where
  structural := e.toControlledIso
  map_payoff := e.map_payoff

end Iso

end ExtensiveGame.ObservedGame
