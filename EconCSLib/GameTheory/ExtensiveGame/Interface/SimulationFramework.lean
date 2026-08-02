/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.PMF
import EconCSLib.GameTheory.ExtensiveGame.Interface.Restart
import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation

/-!
# EconCSLib.GameTheory.ExtensiveGame.Interface.SimulationFramework

Compatibility aggregate import for the complete simulation-oriented
extensive-game framework.

New downstream code should use the smallest stable tier that covers it:

* `Interface.Core` for game forms, execution, and `ObservedGame`;
* `Interface.Execution.Finite` for bounded deterministic and PMF execution;
* `Interface.Execution.Infinite` for measure-valued infinite paths generated
  by discrete PMF policies;
* `Interface.Execution.Discrete` as the historical compatibility name for the
  finite-plus-infinite discrete surface;
* `Interface.Execution.Analytic` for non-atomic measurable-kernel execution
  and analytic presentation assembly;
* `Interface.Relations.Discrete` for strict, refinement, PMF-kernel, and weak
  relations without analytic execution;
* `Interface.Equilibrium.Discrete` for pure, behavioral, mixed, Kuhn,
  designated-root Nash, subgame-perfection-on, and complete standard-SPE
  results;
* `Interface.Equilibrium.Analytic` for measurable-kernel equilibrium and
  continuation;
* `Interface.Restart` for explicit fresh/absolute continuation compatibility;
* `Interface.Compilation.Discrete` for FOSG serialization and concrete
  compilers without analytic equilibrium.

This compatibility-only import path remains supported for existing clients and
CI; its accidental transitive contents are not an independent stability
surface. Relation
extensionality, identity/composition laws, and cast-stable dependent-transport
helpers are available for the normalized game-form, strict-Arena,
observed-isomorphism, and refinement relations. The canonical bounded
designated-continuation Nash entry policy below is stable while implementation
helpers remain outside the public stability promise.

The EFG implementation is organized into five folders: `Execution`,
`Simulation`, `Observed`, `FOSG`, and `Compiler`. Reusable PMF mathematics lives
under `EconCSLib.Math.Probability.PMF`. The separate `Interface` folder contains
public aggregate imports such as this one; the former EFG-local `Probability`
paths are compatibility imports only.

Strict observed-EFG isomorphisms are used for genuine structural relabelings.
Serializers that insert administrative micro-steps instead expose exact
macro-boundary laws through weak/stuttering simulations.

## Canonical bounded designated-continuation entry points

For strict observed-EFG isomorphisms, downstream code should use exactly these
relation-local theorems:

* `ObservedGame.Iso.isPureNashOnRootsAtFuel_iff`;
* `ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff`;
* `ObservedChanceGame.Iso.isMixedNashOnRootsAtFuel_iff`.

Private route regressions in the implementation independently check agreement
of the continuation and refinement layers. They do not add declarations to
this public entry-point list.

Code that is generic over the strategy representation should instead consume
`BoundedDesignatedNashBridge.isNash_iff` and construct the bridge with
`ObservedStrategyBridge.{pure,behavioral,mixed,kuhn}`. This is a uniform
navigation facade over the same canonical theorems, not a second transfer
semantics.
-/
