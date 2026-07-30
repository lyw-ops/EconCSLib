/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior

/-!
# Deprecated state-based behavior-strategy import

The former declarations in this module assigned probability zero to every
action at a chance node. Consequently their `reachProb` lost all mass after
passing through chance and their `expectedPayoff` was not the expectation of a
normalized execution law. The associated state-restart transfer theorem also
assumed the affine payoff decomposition it appeared to derive.

Those declarations have been removed instead of being retained with
mathematically misleading probability and subgame-perfect terminology.

Importing this compatibility path now exposes the canonical replacement:

* `ObservedGame.BehavioralStrategy` is indexed by decision information;
* `ObservedChanceGame.chanceKernel` is a normalized `PMF`;
* `ObservedChanceGame.BehavioralProfile.toHistoryPolicy` combines player and
  chance laws into terminal-aware execution.

Use the stable
`EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium` tier when
equilibrium, continuation, mixed strategies, or Kuhn equivalence are needed.
-/
