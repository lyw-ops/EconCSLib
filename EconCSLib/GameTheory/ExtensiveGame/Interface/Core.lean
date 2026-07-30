/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm
import EconCSLib.GameTheory.ExtensiveGame.Execution.History
import EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution
import EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution
import EconCSLib.GameTheory.ExtensiveGame.Observed.Game
import EconCSLib.GameTheory.ExtensiveGame.Observed.Semantics

/-!
# EconCSLib.GameTheory.ExtensiveGame.Interface.Core

Stable minimal import for representation-neutral game forms, typed execution,
and the core history-indexed observed-game structure.

`ObservedGame.ContinuationSemantics` is the extension boundary for attaching
arbitrary horizon- and outcome-valued evaluators to those history roots.
`ObservedGame.historyInformationPresentation` and
`completeInformationPresentation` provide reducible full-history
presentations; public projection and designated-root selection remain explicit
orthogonal arguments.

This tier intentionally excludes representation relations, equilibrium
transfer, finite Kuhn constructions, FOSG serialization, and concrete
compilers. Downstream developments that only define a new EFG representation
should prefer this import over `SimulationFramework`.
-/
