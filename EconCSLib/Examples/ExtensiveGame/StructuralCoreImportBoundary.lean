/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore

/-!
# Structural-core positive import boundary

The narrow structural facade exposes the game carriers, occurrence-sensitive
history/play types, root presentations, and pure strategies. Its exact
negative source-import boundary is enforced by
`scripts/check_efg_governance.py`.
-/

#check Arena
#check ControlledGame
#check Arena.History
#check Arena.CompletePlayFromHistory
#check ExtensiveGame.ControlledObservedGame
#check ExtensiveGame.ControlledObservedGame.ContinuationRootPresentation
#check ExtensiveGame.ControlledObservedGame.PureStrategy
#check ExtensiveGame.ControlledObservedGame.PureProfile
#check ExtensiveGame.ControlledObservedGame.relabelPlayers
#check ExtensiveGame.ControlledObservedGame.relabelPureProfileEquiv
