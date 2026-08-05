/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete

/-!
# Bounded Kuhn realization with infinite declared information

This one-player game has one represented root information state but declares
`ℕ` as its information carrier. It therefore lies strictly outside
`FiniteKuhnHypotheses`. A direct recall certificate still gives the
countably-supported mixed-to-behavioral equality at every finite fuel.
-/

namespace Examples.InfiniteInformationKuhnBoundary

open ExtensiveGame

/-- Root and terminal endpoints. -/
inductive State
  | root
  | terminal

/-- Two root actions and no terminal action. -/
def action : State → Type
  | .root => Bool
  | .terminal => Empty

def next : (state : State) → action state → State
  | .root, _ => .terminal
  | .terminal, impossible => nomatch impossible

def mover : State → Option Unit
  | .root => some ()
  | .terminal => none

/-- One-step endpoint-payoff game. -/
def base : ExtensiveGame Unit Unit where
  State := State
  Action := action
  next := next
  init := .root
  mover := mover
  payoff := fun _ _ => ()

/-- Only information state `0` is represented, while all natural numbers are
valid declared strategy coordinates. -/
def observed : ObservedGame Unit Unit where
  base := base
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := fun _ _ => rfl
  InfoState := fun _ => ℕ
  infoObserve := fun _ _ => ()
  infoAt := fun _history _player _hmover _hnonterminal => 0
  infoAt_observe := fun _ _ _ _ => rfl
  InfoAction := fun _ _information => Bool
  actionEquiv := by
    intro history player hmover _hnonterminal
    cases player
    cases hstate : history.1 with
    | root =>
        change Bool ≃ Bool
        exact Equiv.refl Bool
    | terminal =>
        change mover history.1 = some () at hmover
        rw [hstate] at hmover
        exact (Option.some_ne_none () hmover.symm).elim

/-- No chance-controlled history exists. -/
def game : ObservedChanceGame Unit Unit where
  observed := observed
  chanceKernel := by
    intro history hchance
    cases hstate : history.1 with
    | root =>
        have hmover := hchance.1
        change mover history.1 = none at hmover
        rw [hstate] at hmover
        exact (Option.some_ne_none () hmover).elim
    | terminal =>
        apply (hchance.2 ?_).elim
        rw [hstate]
        exact ⟨Empty.elim⟩

noncomputable local instance terminalDecidable :
    (state : game.observed.base.State) →
      Decidable (game.observed.base.isTerminal state) :=
  fun _state => Classical.propDecidable _

noncomputable local instance observedTerminalDecidable :
    (state : observed.base.State) →
      Decidable (observed.base.isTerminal state) :=
  fun _state => Classical.propDecidable _

/-- Every represented decision is the root and has no prior personal
decision. -/
def recallCertificate : observed.RecallCertificate where
  remembered := fun _player _information => []
  remembered_infoAt := by
    intro player history hmover _hnonterminal
    cases player
    rcases history with ⟨state, path⟩
    cases path with
    | nil =>
        rfl
    | @snoc previous path previousAction =>
        cases previous with
        | root =>
            change mover (next .root previousAction) = some () at hmover
            simp [next, mover] at hmover
        | terminal =>
            exact Empty.elim previousAction

/-- The declared information carrier is genuinely infinite, so the old
finite-information hypothesis cannot be constructed. -/
theorem infoState_not_finite :
    ¬ Finite (observed.InfoState ()) := by
  change ¬ Finite ℕ
  exact not_finite_iff_infinite.mpr inferInstance

/-- A countably supported mixed plan over the infinite contingent table. -/
noncomputable def mixedProfile : observed.MixedProfile :=
  fun _player => PMF.pure (fun _information => false)

/-- Empty absolute root history. -/
def root : observed.base.History :=
  Arena.HistoryFrom.nil base.toArena base.init

/-- The beyond-finite theorem applies at every bounded horizon despite the
infinite declared information carrier. -/
theorem bounded_history_realization (fuel : ℕ) :
    game.mixedStoppedHistoryLawFrom mixedProfile root fuel =
      observed.base.toArena.stochasticHistoryPMFFrom
        (ObservedChanceGame.BehavioralProfile.toHistoryPolicy game
          (recallCertificate.behavioralizeMixedProfileFrom
            observed root mixedProfile))
        root fuel :=
  game.countablySupportedMixedToBehavioral_boundedHistoryLaw
    recallCertificate mixedProfile root fuel

end Examples.InfiniteInformationKuhnBoundary
