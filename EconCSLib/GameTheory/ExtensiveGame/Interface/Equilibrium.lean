/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic
import EconCSLib.GameTheory.ExtensiveGame.Interface.Relations

/-!
# EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium

Compatibility aggregate for discrete and analytic equilibrium semantics.

Finite-fuel pure, behavioral, mixed, Kuhn, and structural-transfer clients
should import `Interface.Equilibrium.Discrete`. Measurable-kernel clients
should import `Interface.Equilibrium.Analytic`. This established path retains
the union of both surfaces for downstream compatibility.

The discrete layer supplies bounded and termination-certified equilibrium
predicates, subgame perfection on explicit lawful systems, complete standard
SPE, perfect recall, realization morphisms, and constructive finite Kuhn
bridges. The analytic layer adds explicitly measurable and integrable path
utility and constructive Nash predicates for kernel-valued observed profiles.
The measurable-kernel continuation layer adds canonical absolute-clock,
full-event-prefix continuation laws, Nash on presentation-designated roots,
subgame perfection on an explicit lawful system, and complete standard SPE.
Fresh-clock restart laws are available from the separate `Interface.Restart`
tier. Under an explicit standard-Borel future-path
assumption, the conditional layer identifies constructive continuation with
the regular conditional shifted path law almost everywhere and pointwise at
positive-mass finite prefixes; it makes no pointwise claim at null histories.
`ObservedStrategyBridge` exposes pure, behavioral, mixed, and Kuhn Nash
transfer on presentation-designated continuations through one uniform
`BoundedDesignatedNashBridge` interface. FOSG serialization and concrete
compilers remain in the separate `Interface.Compilation` tier.
-/
