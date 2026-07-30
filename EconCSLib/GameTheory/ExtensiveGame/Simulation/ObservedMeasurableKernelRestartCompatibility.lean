/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Equilibrium

/-!
# Fresh-restart compatibility implementation aggregate

Implementation aggregate for the complete fresh-restart proof stack.
Downstream clients should import `Interface.Restart`; declarations in this
aggregate are not individually covered by the stable API promise.

The implementation follows one dependency-ordered route:

* `Restart.Core` normalizes root markers and defines
  measurable path/prefix splicing;
* `.Trajectory` constructs the raw spliced path and finite-prefix laws;
* `.Certificates` converts local raw certificates to trajectory equality;
* `.Observed` lifts them to the canonical state-law compatibility target;
* `.Assembly` requires that target for the baseline and all deviations;
* `.Equilibrium` maintains the single canonical bounded-utility
  designated-continuation Nash, subgame-perfection-on, and complete
  standard-SPE transfer route. Certificate-specific route regressions are
  private.

Ordinary users should start from state-law compatibility, deviation-complete
compatibility, or the canonical `_of_compatible` designated-continuation Nash,
subgame-perfection-on, and complete standard-SPE theorems. The
recommended sufficient constructors are generated-law almost-everywhere step
compatibility and rooted behavioral action-kernel compatibility.  Splicing,
finite marginals, partial-step recurrence, rooted prefix/path steps, and
global pointwise strengthenings are implementation proof tools and may be
renamed or reorganized.

Statistic factorization and time-varying information rebasing are provided by
the sibling implementation leaf `Restart.Factorization`.
-/
