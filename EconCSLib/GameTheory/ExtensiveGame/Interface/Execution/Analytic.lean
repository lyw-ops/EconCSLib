/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Analytic
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Arena
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Execution
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Endpoint
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.StatePath
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.DiscreteBridge
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.HistoryPath
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EventPath
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.ObservedEvent
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.RealizedInformation
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.KernelBridge
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Realized
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.MeasurableHistory
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.Core
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.ProfileAssembly
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Measurable
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.ProfileAssembly
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Countable

/-!
# Analytic measurable-kernel EFG execution

Recommended pre-stability import for normalized non-atomic measurable-kernel
dynamics, terminal-aware execution, finite endpoint and infinite event-time
path laws, state/history/event/information-dependent action policies,
abstract-action realization, and observed profile assembly.

`Controlled.Law.Analytic` packages a measurable-kernel profile assembly into
the same lawful `ControlledObservedGame.CompletePathLawSemantics` used by the
discrete behavioral constructor; canonical deterministic-history legality is
an explicit adapter premise.

`Arena.pathLaw_eq_historyKernelArena_toMeasurable_pathMeasure` identifies the
complete discrete history-path law with the analytic path measure after the
canonical history-state lift. Thus the discrete embedding has a proved
whole-path coherence theorem, rather than merely single-coordinate
agreement. This does not assert a path-law equivalence for every non-atomic
presentation; those presentations enter the common carrier through their
own explicit adapter evidence.

Legality is stated as genuine almost-sure membership in dependent action
fibers. Numerical measure-one lemmas require local measurability assumptions.
This tier supplies execution and presentation semantics only. The discrete
`KernelTrajectory` implementation is transitively visible because exact
discrete recovery uses its policy and finite-law infrastructure, but supported
representation relations, information refinements, equilibrium predicates,
continuation conditioning, and fresh restart belong to later tiers.
-/
