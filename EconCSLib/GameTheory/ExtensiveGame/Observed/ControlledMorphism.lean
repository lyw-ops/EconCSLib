/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledMorphism.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledMorphism.Subgame
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledMorphism.Recall

/-!
# Controlled observed-game morphisms (compatibility aggregate)

This established import path re-exports the structural, lawful-subgame, and
recall leaves. New internal code should import the narrowest
`Observed.ControlledMorphism.*` leaf that provides the declarations it uses.
-/
