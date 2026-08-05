/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Equilibrium
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Factorization

/-!
# Fresh-restart compatibility

Recommended pre-stability import for comparing fresh-clock restart semantics
with absolute-prefix continuation semantics.

The tier requires explicit compatibility for the baseline profile and every
admitted unilateral deviation. Its governed semantic surface is state-law
compatibility, deviation-complete compatibility at/on roots, and the canonical
rootwise, designated-root, subgame-perfection-on, and complete standard-SPE
`_of_compatible` transfers. Generated-law a.e. steps, rooted action kernels,
statistic factorization, and time-varying information rebasing are the
recommended constructors.

Transitive implementation declarations for splicing, finite prefixes,
partial trajectories, and certificate conversion remain available to proofs
but are not individually governed contracts. Certificate-specific equilibrium
wrappers are private; convert a certificate to state-law compatibility and
use the canonical transfer theorem. This tier makes no automatic
identification of the two clocks and no pointwise conditioning claim at null
histories.
-/
