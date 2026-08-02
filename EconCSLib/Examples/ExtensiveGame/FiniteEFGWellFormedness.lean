/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.WellFormed

/-!
# Finite-EFG well-formedness regressions

These examples show why full decision-information representation is a real
finite-profile hypothesis rather than decorative metadata.

Both presentations use the same one-state terminal base game. The first
declares a ghost Boolean information carrier and fails
`AllDecisionInfoRepresented`. The second uses an empty decision-information
carrier, satisfies the structural finite-EFG certificate, and consequently
has an inhabited total pure-profile type.
-/

namespace FiniteEFGWellFormedness

def terminalArena : Arena where
  State := Unit
  Action := fun _ => Empty
  next := fun _ action => action.elim

def terminalBase : ExtensiveGame Unit Unit where
  toArena := terminalArena
  init := ()
  mover := fun _ => none
  payoff := fun _ _ => ()

/-- The canonical complete-information presentation uses only genuine player
decision histories as strategy coordinates. -/
def canonicalTerminalGame : ExtensiveGame.ObservedGame Unit Unit :=
  ExtensiveGame.ObservedGame.completeInformation terminalBase

theorem canonicalTerminalGame_allDecisionInfoRepresented :
    canonicalTerminalGame.AllDecisionInfoRepresented :=
  ExtensiveGame.ObservedGame.completeInformation_allDecisionInfoRepresented
    terminalBase

theorem canonicalTerminalGame_decisionMoverCoherent :
    canonicalTerminalGame.DecisionMoverCoherent := by
  intro _history _i hmover
  simp [canonicalTerminalGame, terminalBase] at hmover

/-- Regression for the former all-history carrier bug: a terminal canonical
presentation now has an inhabited pure-profile type. -/
theorem canonicalTerminalGame_pureProfile_nonempty :
    Nonempty canonicalTerminalGame.PureProfile :=
  ExtensiveGame.ObservedGame.completeInformation_nonempty_pureProfile
    terminalBase
    canonicalTerminalGame_decisionMoverCoherent

/-- The unconstrained base carrier also permits a semantically ignored player
label at a terminal state. -/
def playerLabeledTerminalBase : ExtensiveGame Unit Unit where
  toArena := terminalArena
  init := ()
  mover := fun _ => some ()
  payoff := fun _ _ => ()

def playerLabeledCanonicalTerminalGame :
    ExtensiveGame.ObservedGame Unit Unit :=
  ExtensiveGame.ObservedGame.completeInformation
    playerLabeledTerminalBase

/-- Mover coherence detects the player label on an empty terminal action
fiber. -/
theorem playerLabeledCanonicalTerminalGame_not_decisionMoverCoherent :
    ¬ playerLabeledCanonicalTerminalGame.DecisionMoverCoherent := by
  intro hcoherent
  have hnonempty :=
    hcoherent
      (Arena.HistoryFrom.nil terminalArena ())
      () rfl
  rcases hnonempty with ⟨action⟩
  exact action.elim

/-- Without mover coherence, even the decision-history presentation honestly
exposes the ill-formed terminal decision and its pure-profile type is empty.
-/
theorem playerLabeledCanonicalTerminalGame_pureProfile_empty :
    IsEmpty playerLabeledCanonicalTerminalGame.PureProfile := by
  constructor
  intro profile
  have action :=
    profile ()
      (⟨Arena.HistoryFrom.nil terminalArena (), rfl⟩ :
        playerLabeledCanonicalTerminalGame.InfoState ())
  exact action.elim

/-- A presentation with decision-information values that are never realized.
-/
def ghostGame : ExtensiveGame.ObservedGame Unit Unit where
  base := terminalBase
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := by simp
  InfoState := fun _ => Bool
  infoObserve := fun _ _ => ()
  infoAt := fun _ _ _ => false
  infoAt_observe := by simp
  InfoAction := fun _ _ => Empty
  actionEquiv := fun _ _ _ => Equiv.refl Empty

/-- Ghost decision information is rejected even though the compact base game
is finite and terminal. -/
theorem ghostGame_not_allDecisionInfoRepresented :
    ¬ ghostGame.AllDecisionInfoRepresented := by
  intro hrepresented
  rcases hrepresented () false with ⟨witness⟩
  have hmover := witness.mover
  simp [ghostGame, terminalBase] at hmover

/-- A presentation with no declared decision information, matching the fact
that the base has no player decision histories. -/
def cleanGame : ExtensiveGame.ObservedGame Unit Unit where
  base := terminalBase
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := by simp
  InfoState := fun _ => Empty
  infoObserve := fun _ information => information.elim
  infoAt := fun _ _ hmover => by
    simp [terminalBase] at hmover
  infoAt_observe := by
    intro _ _ hmover
    simp [terminalBase] at hmover
  InfoAction := fun _ information => information.elim
  actionEquiv := fun _ _ hmover => by
    simp [terminalBase] at hmover

theorem cleanGame_allDecisionInfoRepresented :
    cleanGame.AllDecisionInfoRepresented := by
  intro _ information
  exact information.elim

theorem cleanGame_decisionMoverCoherent :
    cleanGame.DecisionMoverCoherent := by
  intro _history _i hmover
  simp [cleanGame, terminalBase] at hmover

/-- The clean terminal presentation has a zero-step finite-EFG certificate.
-/
def cleanGame_finiteEFG :
    cleanGame.FiniteEFGHypotheses where
  lengthBound := 0
  hasLengthBound :=
    Arena.HasLengthBoundAt.of_terminal
      (current :=
        Arena.HistoryFrom.nil
          cleanGame.base.toArena cleanGame.base.init)
      (by
        change IsEmpty Empty
        infer_instance)
  finiteAction := by
    intro history
    change Finite Empty
    infer_instance
  finiteInfoState := by
    intro _i
    change Finite Empty
    infer_instance
  allDecisionInfoRepresented :=
    cleanGame_allDecisionInfoRepresented
  decisionMoverCoherent :=
    cleanGame_decisionMoverCoherent

/-- The finite certificate rules out an accidentally empty pure-profile
carrier. -/
theorem cleanGame_pureProfile_nonempty :
    Nonempty cleanGame.PureProfile :=
  cleanGame_finiteEFG.nonempty_pureProfile

end FiniteEFGWellFormedness
