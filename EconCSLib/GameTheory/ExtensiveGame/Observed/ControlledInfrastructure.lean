/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledInfrastructure.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledInfrastructure.WellFormed
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledInfrastructure.Subgame
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledInfrastructure.Finite
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledInfrastructure.Quasi
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledInfrastructure.Recall
import EconCSLib.GameTheory.ExtensiveGame.Winning.Basic

/-!
# Controlled observed-game infrastructure compatibility aggregate

API role: **legacy import aggregate**. It owns no declarations and must not be
used as an implementation dependency.

Compatibility import for the historical mixed-responsibility
`Observed.ControlledInfrastructure` path. New implementation modules should
import the defining `ControlledInfrastructure.*` leaf, and winning-dependent
quasistrategy predicates belong to `Winning.Basic`.

This module intentionally contains imports and documentation only.
-/
