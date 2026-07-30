/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium
import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete

/-!
# EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation

Compatibility aggregate for reference compilers and analytic equilibrium.

Finite and PMF-valued compiler clients should import
`Interface.Compilation.Discrete`, which extends
`Interface.Equilibrium.Discrete` with concrete observed-EFG adapters and the
weak/stuttering micro-to-macro semantics needed by sequentialization. This
established path retains its former analytic-equilibrium closure for
compatibility. Fresh-restart compatibility is an independent branch in
`Interface.Restart`; clients needing the complete historical stack can import
`Interface.SimulationFramework`.
-/
