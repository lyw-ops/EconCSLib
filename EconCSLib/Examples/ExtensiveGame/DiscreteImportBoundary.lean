/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Discrete

/-!
# Discrete/analytic import boundary

The historical discrete aggregate provides PMF-valued kernel arenas and
measure-valued infinite natural-number event-time execution. Bounded clients
can avoid that measure dependency through `Interface.Execution.Finite`;
genuine non-atomic measurable-kernel arenas remain opt-in through
`Interface.Execution.Analytic`.
-/

#check KernelArena
#check Arena.pathLaw

/--
error: Unknown identifier `MeasurableKernelArena`
-/
#guard_msgs in
#check MeasurableKernelArena
