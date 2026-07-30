/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.StatePath

/-!
# Terminal and nonterminal measurable-kernel endpoint regression

A two-state discrete arena whose active state moves deterministically to a
terminal state.  Its analytic embedding checks both sides of the
terminal-aware execution boundary in one concrete model:

* one endpoint step from `active` is the Dirac law at `terminal`;
* every finite endpoint from `terminal` remains the Dirac law there.

This example is a regression for stopped execution and does not add a new
semantic interface.
-/

open MeasureTheory ProbabilityTheory

namespace EconCSLib.Examples.ExtensiveGame.TerminalKernelBoundary

/-- One active state and one absorbing terminal state. -/
inductive State
  | active
  | terminal
  deriving DecidableEq

/-- The active state has one action; the terminal state has none. -/
def Action : State → Type
  | .active => Unit
  | .terminal => Empty

/-- The unique active action moves deterministically to the terminal state. -/
noncomputable def arena : KernelArena where
  State := State
  Action := Action
  next
    | .active, _ => PMF.pure .terminal
    | .terminal, action => nomatch action

/-- The unique terminal-aware policy of the two-state arena. -/
noncomputable def policy : arena.Policy :=
  fun state hnonterminal =>
    match state with
    | .active => PMF.pure Unit.unit
    | .terminal =>
        (hnonterminal (inferInstance : IsEmpty Empty)).elim

/-- One stopped PMF step from the active state reaches the terminal state. -/
@[simp]
theorem stateLawFrom_one_active :
    arena.stateLawFrom policy 1 .active =
      (pure .terminal : PMF State) := by
  simp [KernelArena.stateLawFrom, KernelArena.stepLaw, arena, policy,
    Action]

/-- The analytic endpoint embedding reproduces the active-to-terminal move
exactly. -/
@[simp]
theorem endpointMeasure_one_active :
    policy.toMeasurable.endpointMeasure
        arena.toMeasurable_measurableSet_terminalSet 1 .active =
      @Measure.dirac State ⊤ .terminal := by
  rw [KernelArena.Policy.toMeasurable_endpointMeasure]
  rw [stateLawFrom_one_active]
  exact @PMF.toMeasure_pure State .terminal ⊤

/-- The terminal state is absorbing at every analytic endpoint horizon. -/
@[simp]
theorem endpointMeasure_terminal (horizon : ℕ) :
    policy.toMeasurable.endpointMeasure
        arena.toMeasurable_measurableSet_terminalSet
        horizon .terminal =
      @Measure.dirac State ⊤ .terminal := by
  apply
    MeasurableKernelArena.ActionPolicy.endpointMeasure_terminal
  change IsEmpty Empty
  exact inferInstance

/-- Starting from the terminal state gives the constant terminal path almost
surely. -/
theorem path_eq_terminal_ae :
    ∀ᵐ path ∂policy.toMeasurable.pathMeasure
        arena.toMeasurable_measurableSet_terminalSet .terminal,
      path = fun _ => State.terminal := by
  letI : MeasurableSingletonClass arena.toMeasurable.State :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  apply
    MeasurableKernelArena.ActionPolicy.ae_path_eq_const_of_terminal
  change IsEmpty Empty
  exact inferInstance

end EconCSLib.Examples.ExtensiveGame.TerminalKernelBoundary
