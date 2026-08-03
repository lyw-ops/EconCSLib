/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled

/-!
# Terminal mover labels do not create strategy coordinates

Regression test for the payoff-free observed-game carrier. A terminal state
may retain an unnormalized player mover label in `ControlledGame`, but it must
not create an impossible pure-strategy obligation.
-/

namespace EconCSLib.Examples.ExtensiveGame.TerminalMoverIgnored

/-- A one-state terminal controlled game whose ignored mover label is
`some ()`. -/
def terminalBase : ControlledGame Unit where
  State := Unit
  Action := fun _ => PEmpty
  next := fun _ action => nomatch action
  init := ()
  mover := fun _ => some ()

/-- The complete-information presentation of `terminalBase`. -/
def observed : _root_.ExtensiveGame.ControlledObservedGame Unit :=
  _root_.ExtensiveGame.ControlledObservedGame.completeInformation terminalBase

/-- There are no decision-information states, despite the terminal mover
label. -/
theorem infoState_isEmpty : IsEmpty (observed.InfoState ()) := by
  constructor
  intro information
  exact information.2.2 ⟨fun action => nomatch action⟩

/-- Consequently, a pure strategy exists without selecting an action at the
terminal state. -/
def pureStrategy : observed.PureStrategy () :=
  fun information => (infoState_isEmpty.false information).elim

/-- The corresponding one-player profile exists as well. -/
def pureProfile : observed.PureProfile :=
  fun _ => pureStrategy

end EconCSLib.Examples.ExtensiveGame.TerminalMoverIgnored
