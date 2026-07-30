/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution

/-!
# EconCSLib.GameTheory.ExtensiveGame.Play (deprecated compatibility import)

The former `Arena.play` API required an action at every state, including
terminal states whose action type is empty, and therefore did not model
terminal execution correctly.  It has been removed rather than retained under
a misleading name.

Importing this module now exposes the terminal-aware execution API from
`Execution.StoppedExecution`:

* `Arena.HistoryPolicy` is queried only at nonterminal endpoints;
* `Arena.stoppedHistoryFrom` and `Arena.stoppedHistory` stop at terminals;
* `ExtensiveGame.stoppedPayoff` returns a payoff only after termination.

New code should import
`EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Discrete` or
`EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution` directly.
-/
