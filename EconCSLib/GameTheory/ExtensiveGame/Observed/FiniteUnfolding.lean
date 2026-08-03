/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Objective
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Finite
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Discrete
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Subgame
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Recall
import EconCSLib.GameTheory.ExtensiveGame.Observed.WellFormed
import EconCSLib.GameTheory.ExtensiveGame.Winning.Basic
import Mathlib.Tactic

/-!
# Finite occurrence-sensitive reachable unfolding

`FiniteEFGHypotheses` does not require a finite ambient state space.  Its
uniform history-length bound and locally finite legal actions instead make the
reachable complete-history carrier finite.  This module constructs that
carrier and an ordinary finite-state `ExtensiveGame` whose states are bounded
complete histories.

The construction never quotients by endpoint state.  Distinct histories that
merge in the compact arena remain distinct states of the finite unfolding.
Private/public observations, information states, chance laws, and
history-sensitive terminal outcomes are pulled back through
`originalHistory`; they are not recomputed from the compact endpoint.

The output is suitable as the finite carrier consumed by backward-induction,
normal-form, and finite-determinacy developments.  Algorithms still add their
own player finiteness, decision procedures, preference data, and solution
concept assumptions.

## Main definitions

* `Arena.HistoryOfLengthFrom`.
* `Arena.BoundedHistoryFrom`.
* `Arena.boundedUnfolding`.
* `ObservedGame.FiniteEFGHypotheses.toFiniteHistoryGame`.

## Main results

* bounded exact-length histories are finite under locally finite actions;
* every history lies below a declared structural length bound;
* the finite unfolding has finite states and finite actions;
* transitions, movers, payoffs, observations, information, and structural
  length are preserved through the original-history projection.
-/

namespace Arena

universe uA uS

variable {A : Arena} {start : A.State}

/-- Complete histories having exactly `length` action occurrences. -/
abbrev HistoryOfLengthFrom
    (A : Arena) (start : A.State) (length : ℕ) :=
  {history : A.HistoryFrom start //
    history.2.length = length}

/-- Complete histories having at most `bound` action occurrences. -/
abbrev BoundedHistoryFrom
    (A : Arena) (start : A.State) (bound : ℕ) :=
  {history : A.HistoryFrom start //
    history.2.length ≤ bound}

/-- There is only one zero-length complete history. -/
theorem historyOfLengthFrom_zero_subsingleton
    (A : Arena) (start : A.State) :
    Subsingleton (A.HistoryOfLengthFrom start 0) := by
  constructor
  intro first second
  have hfirst :
      first.1 = HistoryFrom.nil A start := by
    rcases first with ⟨⟨finish, history⟩, hlength⟩
    cases history with
    | nil =>
        rfl
    | snoc history action =>
        simp at hlength
  have hsecond :
      second.1 = HistoryFrom.nil A start := by
    rcases second with ⟨⟨finish, history⟩, hlength⟩
    cases history with
    | nil =>
        rfl
    | snoc history action =>
        simp at hlength
  exact Subtype.ext (hfirst.trans hsecond.symm)

/-- Exact-length complete histories are finite when legal actions are finite
at every represented history. -/
@[implicit_reducible]
noncomputable def finiteHistoryOfLengthFrom
    (finiteAction :
      ∀ history : A.HistoryFrom start,
        Finite (A.Action history.1)) :
    ∀ length : ℕ,
      Finite (A.HistoryOfLengthFrom start length)
  | 0 => by
      letI :
          Subsingleton
            (A.HistoryOfLengthFrom start 0) :=
        historyOfLengthFrom_zero_subsingleton A start
      exact Finite.of_subsingleton
  | length + 1 => by
      letI :
          Finite
            (A.HistoryOfLengthFrom start length) :=
        finiteHistoryOfLengthFrom finiteAction length
      letI (history :
          A.HistoryOfLengthFrom start length) :
          Finite (A.Action history.1.1) :=
        finiteAction history.1
      let extend :
          (Σ history :
              A.HistoryOfLengthFrom start length,
            A.Action history.1.1) →
            A.HistoryOfLengthFrom start (length + 1) :=
        fun ⟨history, action⟩ =>
          ⟨⟨A.next history.1.1 action,
              history.1.2.snoc action⟩,
            by simp [history.2]⟩
      apply Finite.of_surjective extend
      intro target
      rcases target with
        ⟨⟨finish, history⟩, hlength⟩
      cases history with
      | nil =>
          simp at hlength
      | @snoc previousState path action =>
          have hprefix :
              path.length = length := by
            simp only [History.length_snoc] at hlength
            omega
          refine
            ⟨⟨⟨⟨previousState, path⟩, hprefix⟩,
                action⟩, ?_⟩
          apply Subtype.ext
          rfl

/-- Bounded complete histories form a finite type under locally finite legal
actions. -/
@[implicit_reducible]
noncomputable def finiteBoundedHistoryFrom
    (finiteAction :
      ∀ history : A.HistoryFrom start,
        Finite (A.Action history.1))
    (bound : ℕ) :
    Finite (A.BoundedHistoryFrom start bound) := by
  letI (length : ℕ) :
      Finite (A.HistoryOfLengthFrom start length) :=
    finiteHistoryOfLengthFrom finiteAction length
  let encode :
      A.BoundedHistoryFrom start bound →
        Σ length : Fin (bound + 1),
          A.HistoryOfLengthFrom start length :=
    fun history =>
      ⟨⟨history.1.2.length,
          Nat.lt_succ_iff.mpr history.2⟩,
        ⟨history.1, rfl⟩⟩
  apply Finite.of_injective encode
  intro first second heq
  apply Subtype.ext
  exact congrArg (fun encoded => encoded.2.1) heq

/-- A structural root length bound bounds every legal complete history, not
only histories generated by a selected policy. -/
theorem History.length_le_of_hasLengthBoundFrom
    {finish : A.State}
    {bound : ℕ}
    (hbound : A.HasLengthBoundFrom start bound)
    (history : A.History start finish) :
    history.length ≤ bound := by
  induction history with
  | nil =>
      exact Nat.zero_le _
  | @snoc previousState path action ih =>
      have hne : path.length ≠ bound := by
        intro heq
        exact (hbound path heq).false action
      simp only [History.length_snoc]
      omega

/-- Appending one legal action stays inside the bounded history carrier. -/
def BoundedHistoryFrom.snoc
    {bound : ℕ}
    (hbound : A.HasLengthBoundFrom start bound)
    (history : A.BoundedHistoryFrom start bound)
    (action : A.Action history.1.1) :
    A.BoundedHistoryFrom start bound :=
  ⟨⟨A.next history.1.1 action,
      history.1.2.snoc action⟩,
    History.length_le_of_hasLengthBoundFrom
      hbound (history.1.2.snoc action)⟩

/-- Finite occurrence-sensitive unfolding truncated at a certified structural
bound.

Every state is a complete history.  The bound is used only to make the state
carrier finite; legal actions and transitions are inherited exactly. -/
def boundedUnfolding
    (A : Arena) (start : A.State) (bound : ℕ)
    (hbound : A.HasLengthBoundFrom start bound) :
    Arena where
  State := A.BoundedHistoryFrom start bound
  Action := fun history => A.Action history.1.1
  next := fun history action =>
    history.snoc hbound action

/-- Project one bounded-unfolding state to its original complete history. -/
def boundedUnfoldingOriginalHistory
    {bound : ℕ}
    {hbound : A.HasLengthBoundFrom start bound}
    (history : (A.boundedUnfolding start bound hbound).State) :
    A.HistoryFrom start :=
  history.1

@[simp]
theorem boundedUnfoldingOriginalHistory_next
    {bound : ℕ}
    {hbound : A.HasLengthBoundFrom start bound}
    (history : (A.boundedUnfolding start bound hbound).State)
    (action :
      (A.boundedUnfolding start bound hbound).Action history) :
    boundedUnfoldingOriginalHistory
        ((A.boundedUnfolding start bound hbound).next
          history action) =
      ⟨A.next history.1.1 action,
        history.1.2.snoc action⟩ :=
  rfl

/-- A history in the finite unfolding has the same length as the original
complete history stored at its endpoint. -/
theorem boundedUnfolding_history_length
    {bound : ℕ}
    {hbound : A.HasLengthBoundFrom start bound}
    {finish :
      (A.boundedUnfolding start bound hbound).State}
    (history :
      (A.boundedUnfolding start bound hbound).History
        ⟨HistoryFrom.nil A start, Nat.zero_le bound⟩
        finish) :
    finish.1.2.length = history.length := by
  induction history with
  | nil =>
      rfl
  | snoc history action ih =>
      simp [boundedUnfolding,
        BoundedHistoryFrom.snoc, ih]

/-- The bounded unfolding inherits the declared structural length bound. -/
theorem boundedUnfolding_hasLengthBoundFrom
    {bound : ℕ}
    (hbound : A.HasLengthBoundFrom start bound) :
    (A.boundedUnfolding start bound hbound).HasLengthBoundFrom
        ⟨HistoryFrom.nil A start, Nat.zero_le bound⟩
        bound := by
  intro finish history hlength
  change IsEmpty (A.Action finish.1.1)
  apply hbound finish.1.2
  exact
    (boundedUnfolding_history_length history).trans
      hlength

end Arena

namespace ExtensiveGame.ObservedGame.FiniteEFGHypotheses

variable {N U : Type*} {G : ObservedGame N U}

/-- The finite occurrence-sensitive history game extracted from a structural
finite-EFG certificate. -/
noncomputable def toFiniteHistoryGame
    (h : G.FiniteEFGHypotheses) :
    ExtensiveGame N U :=
  ExtensiveGame.ofArena
    (G.base.toArena.boundedUnfolding
      G.base.init h.lengthBound h.hasLengthBound)
    ⟨Arena.HistoryFrom.nil G.base.toArena G.base.init,
      Nat.zero_le h.lengthBound⟩
    (fun history => G.base.mover history.1.1)
    (fun history => G.base.payoff history.1.1)

/-- Original complete history represented by one finite-unfolding state. -/
def originalHistory
    (h : G.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State) :
    G.base.toArena.HistoryFrom G.base.init :=
  state.1

/-- The finite unfolding has a finite state carrier even when the ambient
compact state type is infinite. -/
noncomputable instance finiteState
    (h : G.FiniteEFGHypotheses) :
    Fintype h.toFiniteHistoryGame.State := by
  change Fintype
    (G.base.toArena.BoundedHistoryFrom
      G.base.init h.lengthBound)
  letI : Finite
      (G.base.toArena.BoundedHistoryFrom
        G.base.init h.lengthBound) :=
    Arena.finiteBoundedHistoryFrom
      h.finiteAction h.lengthBound
  exact Fintype.ofFinite _

/-- Legal actions remain finite at every finite-unfolding state. -/
noncomputable instance finiteUnfoldingAction
    (h : G.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State) :
    Fintype (h.toFiniteHistoryGame.Action state) := by
  change Fintype (G.base.Action state.1.1)
  letI : Finite (G.base.Action state.1.1) :=
    h.finiteAction state.1
  exact Fintype.ofFinite _

@[simp]
theorem originalHistory_init
    (h : G.FiniteEFGHypotheses) :
    h.originalHistory h.toFiniteHistoryGame.init =
      Arena.HistoryFrom.nil G.base.toArena G.base.init :=
  rfl

@[simp]
theorem originalHistory_next
    (h : G.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State)
    (action : h.toFiniteHistoryGame.Action state) :
    h.originalHistory
        (h.toFiniteHistoryGame.next state action) =
      ⟨G.base.next (h.originalHistory state).1 action,
        (h.originalHistory state).2.snoc action⟩ :=
  rfl

/-- The finite unfolding preserves legal action occurrences definitionally.
-/
def actionEquiv
    (h : G.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State) :
    h.toFiniteHistoryGame.Action state ≃
      G.base.Action (h.originalHistory state).1 :=
  Equiv.refl _

@[simp]
theorem mover_eq
    (h : G.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State) :
    h.toFiniteHistoryGame.mover state =
      G.base.mover (h.originalHistory state).1 :=
  rfl

@[simp]
theorem payoff_eq
    (h : G.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State) :
    h.toFiniteHistoryGame.payoff state =
      G.base.payoff (h.originalHistory state).1 :=
  rfl

/-- Pull back one player's private observation without forgetting the
occurrence-sensitive original history. -/
def privateObservationAt
    (h : G.FiniteEFGHypotheses)
    (i : N) (state : h.toFiniteHistoryGame.State) :
    G.Observation i :=
  G.observe i (h.originalHistory state)

/-- Pull back the public observation through the original-history
projection. -/
def publicObservationAt
    (h : G.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State) :
    G.PublicObservation :=
  G.publicObserve (h.originalHistory state)

/-- Pull back the decision information state at a player-controlled
finite-unfolding state. -/
def informationAt
    (h : G.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State) (i : N)
    (hmover :
      h.toFiniteHistoryGame.mover state = some i) :
    G.InfoState i :=
  G.infoAt (h.originalHistory state) i hmover

/-- The pulled-back private observation has exactly the original public
component. -/
theorem privateObservation_public
    (h : G.FiniteEFGHypotheses)
    (i : N) (state : h.toFiniteHistoryGame.State) :
    G.publicOf i (h.privateObservationAt i state) =
      h.publicObservationAt state :=
  G.observe_public i (h.originalHistory state)

/-- The finite occurrence carrier equipped with the original observation and
decision-information presentation.

Every observation is evaluated at the full original history stored in the
finite endpoint, so merging ambient states does not merge information. -/
noncomputable def toFiniteObservedGame
    (h : G.FiniteEFGHypotheses) :
    ObservedGame N U where
  base := h.toFiniteHistoryGame
  Observation := G.Observation
  PublicObservation := G.PublicObservation
  observe := fun i history =>
    G.observe i (h.originalHistory history.1)
  publicObserve := fun history =>
    G.publicObserve (h.originalHistory history.1)
  publicOf := G.publicOf
  observe_public := fun i history =>
    G.observe_public i (h.originalHistory history.1)
  InfoState := G.InfoState
  infoObserve := G.infoObserve
  infoAt := fun history i hmover =>
    G.infoAt (h.originalHistory history.1) i hmover
  infoAt_observe := fun history i hmover =>
    G.infoAt_observe
      (h.originalHistory history.1) i hmover
  InfoAction := G.InfoAction
  actionEquiv := fun history i hmover =>
    G.actionEquiv
      (h.originalHistory history.1) i hmover

/-- Pure contingent plans are definitionally unchanged by finite occurrence
unfolding because information-state and abstract-action families are reused
exactly. -/
def pureStrategyEquiv
    (h : G.FiniteEFGHypotheses) (i : N) :
    h.toFiniteObservedGame.PureStrategy i ≃
      G.PureStrategy i :=
  Equiv.refl _

/-- Behavioral contingent plans are also definitionally unchanged. Thus
componentwise pure and behavioral unilateral replacements use the same
strategy carrier before and after extraction. -/
def behavioralStrategyEquiv
    (h : G.FiniteEFGHypotheses) (i : N) :
    h.toFiniteObservedGame.BehavioralStrategy i ≃
      G.BehavioralStrategy i :=
  Equiv.refl _

/-- Pull an external root presentation back to the finite occurrence
presentation. This records visibility only and makes no standard-subgame
lawfulness claim. -/
def pullRootPresentation
    (h : G.FiniteEFGHypotheses)
    (roots : G.RootPresentation) :
    h.toFiniteObservedGame.RootPresentation where
  IsRoot := fun history =>
    roots.IsRoot (h.originalHistory history.1)
  init_isRoot := by
    simpa using roots.init_isRoot

/-- Pull back a history-sensitive terminal outcome to a terminal state of the
finite unfolding. -/
def pullTerminalOutcome
    (h : G.FiniteEFGHypotheses)
    {Outcome : Type*}
    (outcome :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (state : h.toFiniteHistoryGame.State)
    (hterminal :
      h.toFiniteHistoryGame.isTerminal state) :
    Outcome :=
  outcome
    ⟨h.originalHistory state, hterminal⟩

/-- A discrete chance law at a finite-unfolding state is exactly the original
PMF at the represented complete history. -/
def discreteChanceLawAt
    (chanceGame : ObservedChanceGame N U)
    (h : chanceGame.observed.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State)
    (hchance :
      h.toFiniteHistoryGame.mover state = none ∧
        ¬ h.toFiniteHistoryGame.isTerminal state) :
    PMF (h.toFiniteHistoryGame.Action state) :=
  chanceGame.chanceKernel
    (h.originalHistory state) hchance

/-- The finite observed occurrence carrier equipped with exactly the original
discrete chance PMF at every represented chance history. -/
noncomputable def toFiniteObservedChanceGame
    (chanceGame : ObservedChanceGame N U)
    (h : chanceGame.observed.FiniteEFGHypotheses) :
    ObservedChanceGame N U where
  observed := h.toFiniteObservedGame
  chanceKernel := fun history hchance =>
    chanceGame.chanceKernel
      (h.originalHistory history.1) hchance

/-- The extracted finite history game retains the same structural length
bound. -/
theorem toFiniteHistoryGame_hasLengthBound
    (h : G.FiniteEFGHypotheses) :
    h.toFiniteHistoryGame.toArena.HasLengthBoundFrom
      h.toFiniteHistoryGame.init h.lengthBound :=
  Arena.boundedUnfolding_hasLengthBoundFrom h.hasLengthBound

/-- Distinct original complete histories remain distinct unfolding states.
In particular, histories that merge at one compact endpoint are not
identified. -/
theorem state_ne_of_originalHistory_ne
    (h : G.FiniteEFGHypotheses)
    {first second : h.toFiniteHistoryGame.State}
    (hne :
      h.originalHistory first ≠
        h.originalHistory second) :
    first ≠ second := by
  intro heq
  exact hne (congrArg h.originalHistory heq)

end ExtensiveGame.ObservedGame.FiniteEFGHypotheses

namespace ExtensiveGame.ControlledObservedGame.FiniteEFGHypotheses

universe uN uA uS uO uI uP

variable {N : Type uN}
  {G : ControlledObservedGame.{uN, uA, uS, uO, uI, uP} N}

/-- Payoff-free finite occurrence-sensitive history game extracted from a
structural finite-EFG certificate. -/
noncomputable def toFiniteHistoryGame
    (h : G.FiniteEFGHypotheses) :
    ControlledGame.{uN, uS, max uA uS} N :=
  ControlledGame.ofArena
    (G.base.toArena.boundedUnfolding
      G.base.init h.lengthBound h.hasLengthBound)
    ⟨Arena.HistoryFrom.nil G.base.toArena G.base.init,
      Nat.zero_le h.lengthBound⟩
    (fun history => G.base.mover history.1.1)

/-- Original complete history represented by a payoff-free unfolding state. -/
def originalHistory
    (h : G.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State) :
    G.base.History :=
  state.1

@[simp]
theorem originalHistory_init
    (h : G.FiniteEFGHypotheses) :
    h.originalHistory h.toFiniteHistoryGame.init =
      Arena.HistoryFrom.nil G.base.toArena G.base.init :=
  rfl

@[simp]
theorem originalHistory_next
    (h : G.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State)
    (action : h.toFiniteHistoryGame.Action state) :
    h.originalHistory
        (h.toFiniteHistoryGame.next state action) =
      ⟨G.base.next (h.originalHistory state).1 action,
        (h.originalHistory state).2.snoc action⟩ :=
  rfl

/-- Dependent legal-action fibers are preserved exactly. -/
def actionEquiv
    (h : G.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State) :
    h.toFiniteHistoryGame.Action state ≃
      G.base.Action (h.originalHistory state).1 :=
  Equiv.refl _

@[simp]
theorem mover_eq
    (h : G.FiniteEFGHypotheses)
    (state : h.toFiniteHistoryGame.State) :
    h.toFiniteHistoryGame.mover state =
      G.base.mover (h.originalHistory state).1 :=
  rfl

/-- The payoff-free finite occurrence carrier with private/public
observations and decision information evaluated on the full original
history. -/
noncomputable def toFiniteObservedGame
    (h : G.FiniteEFGHypotheses) :
    ControlledObservedGame.{
      uN, max uA uS, uS, uO, uI, uP} N where
  base := h.toFiniteHistoryGame
  Observation := G.Observation
  PublicObservation := G.PublicObservation
  observe := fun i history =>
    G.observe i (h.originalHistory history.1)
  publicObserve := fun history =>
    G.publicObserve (h.originalHistory history.1)
  publicOf := G.publicOf
  observe_public := fun i history =>
    G.observe_public i (h.originalHistory history.1)
  InfoState := G.InfoState
  infoObserve := G.infoObserve
  infoAt := fun history i hmover =>
    G.infoAt (h.originalHistory history.1) i hmover
  infoAt_observe := fun history i hmover =>
    G.infoAt_observe
      (h.originalHistory history.1) i hmover
  InfoAction := fun i information =>
    ULift (G.InfoAction i information)
  actionEquiv := fun history i hmover =>
    { toFun := fun action =>
        G.actionEquiv
          (h.originalHistory history.1) i hmover
          action.down
      invFun := fun action =>
        ULift.up
          ((G.actionEquiv
            (h.originalHistory history.1) i hmover).symm
              action)
      left_inv := by
        intro action
        cases action
        simp
      right_inv := by
        intro action
        simp }

/-- The bounded state representing one original complete history. -/
def boundedState
    (h : G.FiniteEFGHypotheses)
    (history : G.base.History) :
    h.toFiniteHistoryGame.State :=
  ⟨history,
    Arena.History.length_le_of_hasLengthBoundFrom
      h.hasLengthBound history.2⟩

@[simp]
theorem originalHistory_boundedState
    (h : G.FiniteEFGHypotheses)
    (history : G.base.History) :
    h.originalHistory (h.boundedState history) = history :=
  rfl

@[simp]
theorem boundedState_nil
    (h : G.FiniteEFGHypotheses) :
    h.boundedState
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      h.toFiniteHistoryGame.init := by
  apply Subtype.ext
  rfl

@[simp]
theorem boundedState_snoc
    (h : G.FiniteEFGHypotheses)
    (history : G.base.History)
    (action : G.base.Action history.1) :
    h.boundedState
        ⟨G.base.next history.1 action,
          history.2.snoc action⟩ =
      h.toFiniteHistoryGame.next
        (h.boundedState history) action := by
  apply Subtype.ext
  rfl

/-- Canonically lift one original path to the path through its successive
occurrences in the bounded unfolding. -/
def liftPath
    (h : G.FiniteEFGHypotheses) :
    {finish : G.base.State} →
      (path : G.base.toArena.History G.base.init finish) →
        h.toFiniteHistoryGame.toArena.History
          h.toFiniteHistoryGame.init
          (h.boundedState ⟨finish, path⟩)
  | _, .nil => by
      have hstate :
          h.boundedState
              ⟨G.base.init, Arena.History.nil⟩ =
            h.toFiniteHistoryGame.init := by
        apply Subtype.ext
        rfl
      rw [hstate]
      exact Arena.History.nil
  | _, @Arena.History.snoc _ _ state path action => by
      have hstate :
          h.boundedState
              ⟨G.base.next state action, path.snoc action⟩ =
            h.toFiniteHistoryGame.next
              (h.boundedState ⟨state, path⟩) action := by
        apply Subtype.ext
        rfl
      rw [hstate]
      exact (h.liftPath path).snoc action

/-- Canonically lift one original complete history to a complete history of
the bounded occurrence unfolding. -/
def liftHistory
    (h : G.FiniteEFGHypotheses)
    (history : G.base.History) :
    h.toFiniteObservedGame.base.History :=
  ⟨h.boundedState history, h.liftPath history.2⟩

@[simp]
theorem originalHistory_liftHistory
    (h : G.FiniteEFGHypotheses)
    (history : G.base.History) :
    h.originalHistory (h.liftHistory history).1 = history :=
  rfl

@[simp]
theorem liftHistory_nil
    (h : G.FiniteEFGHypotheses) :
    h.liftHistory
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      Arena.HistoryFrom.nil
        h.toFiniteHistoryGame.toArena
        h.toFiniteHistoryGame.init := by
  apply Sigma.ext h.boundedState_nil
  exact HEq.rfl

@[simp]
theorem liftHistory_snoc
    (h : G.FiniteEFGHypotheses)
    (history : G.base.History)
    (action : G.base.Action history.1) :
    h.liftHistory
        ⟨G.base.next history.1 action,
          history.2.snoc action⟩ =
      h.toFiniteObservedGame.base.unfold.toArena.next
        (h.liftHistory history) action := by
  apply Sigma.ext (h.boundedState_snoc history action)
  exact HEq.rfl

/-- Projecting an unfolding history to the original occurrence and
canonically lifting it again is the identity. -/
@[simp]
theorem liftHistory_originalHistory
    (h : G.FiniteEFGHypotheses)
    (history : h.toFiniteObservedGame.base.History) :
    h.liftHistory (h.originalHistory history.1) = history := by
  obtain ⟨finish, path⟩ := history
  induction path with
  | nil =>
      exact h.liftHistory_nil
  | @snoc state path action ih =>
      change
        h.liftHistory
            (h.originalHistory
              (h.toFiniteHistoryGame.next state action)) =
          h.toFiniteObservedGame.base.unfold.toArena.next
            ⟨state, path⟩ action
      rw [h.originalHistory_next]
      rw [h.liftHistory_snoc]
      have hstate :
          (h.liftHistory (h.originalHistory state)).1 =
            state :=
        (Sigma.ext_iff.mp ih).1
      have hpath :
          (h.liftHistory
              (h.originalHistory state)).2 ≍ path :=
        (Sigma.ext_iff.mp ih).2
      cases hstate
      have hpath' :
          (h.liftHistory
              (h.originalHistory state)).2 = path :=
        eq_of_heq hpath
      cases hpath'
      rfl

/-- Complete histories of the finite occurrence unfolding are canonically
equivalent to the original complete histories. -/
def historyEquiv
    (h : G.FiniteEFGHypotheses) :
    h.toFiniteObservedGame.base.History ≃ G.base.History where
  toFun := fun history => h.originalHistory history.1
  invFun := h.liftHistory
  left_inv := h.liftHistory_originalHistory
  right_inv := h.originalHistory_liftHistory

/-- Strict arena isomorphism obtained by projecting a bounded unfolding
history to its occurrence-sensitive original history. -/
def historyArenaIso
    (h : G.FiniteEFGHypotheses) :
    h.toFiniteObservedGame.base.unfold.toArena.Iso
      G.base.unfold.toArena where
  stateEquiv := h.historyEquiv
  actionEquiv := fun _history => Equiv.refl _
  map_next := by
    intro history action
    rfl

/-- The finite occurrence presentation is strictly isomorphic, without any
payoff field, to the original payoff-free observed game. -/
def toOriginalIso
    (h : G.FiniteEFGHypotheses) :
    h.toFiniteObservedGame.Iso G where
  historyIso := h.historyArenaIso
  map_init := rfl
  map_mover := by
    intro history
    rfl
  observationEquiv := fun _i => Equiv.refl _
  map_observe := by
    intro i history
    rfl
  publicEquiv := Equiv.refl _
  map_publicObserve := by
    intro history
    rfl
  map_publicOf := by
    intro i observation
    rfl
  infoStateEquiv := fun _i => Equiv.refl _
  map_infoObserve := by
    intro i information
    rfl
  infoActionEquiv := fun _i _information => Equiv.ulift
  map_infoAt := by
    intro history i hsource htarget
    rfl
  map_infoActionAt := by
    intro history i hsource htarget action
    rfl

/-- Classic perfect recall is preserved and reflected by finite occurrence
unfolding. -/
theorem perfectRecall_iff
    [DecidableEq N]
    (h : G.FiniteEFGHypotheses) :
    h.toFiniteObservedGame.PerfectRecall ↔
      G.PerfectRecall :=
  h.toOriginalIso.perfectRecall_iff

/-- Private-signal perfect recall is preserved and reflected by finite
occurrence unfolding. -/
theorem eventClockSignalPerfectRecall_iff
    (h : G.FiniteEFGHypotheses) :
    h.toFiniteObservedGame.EventClockSignalPerfectRecall ↔
      G.EventClockSignalPerfectRecall :=
  h.toOriginalIso.eventClockSignalPerfectRecall_iff

/-- Public-signal perfect recall is preserved and reflected by finite
occurrence unfolding. -/
theorem eventClockPublicPerfectRecall_iff
    (h : G.FiniteEFGHypotheses) :
    h.toFiniteObservedGame.HasEventClockPublicPerfectRecall ↔
      G.HasEventClockPublicPerfectRecall :=
  h.toOriginalIso.hasEventClockPublicPerfectRecall_iff

/-- Private observation is evaluated on the represented original complete
history. -/
@[simp]
theorem observe_eq
    (h : G.FiniteEFGHypotheses)
    (i : N)
    (history : h.toFiniteObservedGame.base.History) :
    h.toFiniteObservedGame.observe i history =
      G.observe i (h.originalHistory history.1) :=
  rfl

/-- Public observation is evaluated on the represented original complete
history. -/
@[simp]
theorem publicObserve_eq
    (h : G.FiniteEFGHypotheses)
    (history : h.toFiniteObservedGame.base.History) :
    h.toFiniteObservedGame.publicObserve history =
      G.publicObserve (h.originalHistory history.1) :=
  rfl

/-- Decision information is evaluated on the represented original complete
history. -/
@[simp]
theorem infoAt_eq
    (h : G.FiniteEFGHypotheses)
    (history : h.toFiniteObservedGame.base.History)
    (i : N)
    (hmover :
      h.toFiniteObservedGame.base.mover history.1 = some i) :
    h.toFiniteObservedGame.infoAt history i hmover =
      G.infoAt (h.originalHistory history.1) i hmover :=
  rfl

/-- Pure contingent-plan carriers are canonically equivalent under
payoff-free finite occurrence unfolding. -/
def pureStrategyEquiv
    (h : G.FiniteEFGHypotheses) (i : N) :
    h.toFiniteObservedGame.PureStrategy i ≃
      G.PureStrategy i where
  toFun := fun strategy information =>
    (strategy information).down
  invFun := fun strategy information =>
    ULift.up (strategy information)
  left_inv := by
    intro strategy
    funext information
    apply ULift.ext
    rfl
  right_inv := by
    intro strategy
    rfl

/-- Project a complete play of the bounded unfolding to the corresponding
occurrence-sensitive complete play of the original arena. -/
def projectCompletePlay
    (h : G.FiniteEFGHypotheses)
    (play :
      h.toFiniteHistoryGame.toArena.CompletePlayFrom
        h.toFiniteHistoryGame.init) :
    G.base.CompletePlay where
  historyAt := fun time =>
    h.originalHistory (play.historyAt time).1
  historyAt_zero := by
    rw [play.historyAt_zero]
    rfl
  step := by
    intro time
    rcases play.step time with hstutter | hchild
    · left
      exact ⟨hstutter.1, by rw [hstutter.2]⟩
    · right
      rcases hchild with ⟨action, hnext⟩
      refine ⟨action, ?_⟩
      change
        h.originalHistory (play.historyAt (time + 1)).1 =
          ⟨G.base.next
              (h.originalHistory
                (play.historyAt time).1).1 action,
            (h.originalHistory
                (play.historyAt time).1).2.snoc action⟩
      rw [hnext]
      rfl

@[simp]
theorem projectCompletePlay_historyAt
    (h : G.FiniteEFGHypotheses)
    (play :
      h.toFiniteHistoryGame.toArena.CompletePlayFrom
        h.toFiniteHistoryGame.init)
    (time : ℕ) :
    (h.projectCompletePlay play).historyAt time =
      h.originalHistory (play.historyAt time).1 :=
  rfl

/-- Pull a complete-path objective back through occurrence-sensitive complete
play projection. -/
def pullWinningCondition
    (h : G.FiniteEFGHypotheses)
    (W : G.base.WinningCondition) :
    h.toFiniteHistoryGame.WinningCondition :=
  fun i => h.projectCompletePlay ⁻¹' W i

@[simp]
theorem mem_pullWinningCondition_iff
    (h : G.FiniteEFGHypotheses)
    (W : G.base.WinningCondition)
    (i : N)
    (play :
      h.toFiniteHistoryGame.toArena.CompletePlayFrom
        h.toFiniteHistoryGame.init) :
    play ∈ h.pullWinningCondition W i ↔
      h.projectCompletePlay play ∈ W i :=
  Iff.rfl

/-- Map a finite-unfolding pure profile back to the original payoff-free
information carrier. -/
def mapPureProfile
    (h : G.FiniteEFGHypotheses)
    (profile : h.toFiniteObservedGame.PureProfile) :
    G.PureProfile :=
  fun i => h.pureStrategyEquiv i (profile i)

/-- Lift an original pure strategy to the finite unfolding. -/
def liftPureStrategy
    (h : G.FiniteEFGHypotheses)
    {i : N} (strategy : G.PureStrategy i) :
    h.toFiniteObservedGame.PureStrategy i :=
  (h.pureStrategyEquiv i).symm strategy

/-- Pure-profile mapping commutes with every unilateral deviation. -/
theorem mapPureProfile_update
    [DecidableEq N]
    (h : G.FiniteEFGHypotheses)
    (profile : h.toFiniteObservedGame.PureProfile)
    (who : N)
    (deviation :
      h.toFiniteObservedGame.PureStrategy who) :
    h.mapPureProfile
        (Function.update profile who deviation) =
      Function.update (h.mapPureProfile profile) who
        (h.pureStrategyEquiv who deviation) := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [mapPureProfile]
  · simp [mapPureProfile, hi]

/-- Pull an external payoff-free root presentation back without changing its
selected original histories. -/
def pullRootPresentation
    (h : G.FiniteEFGHypotheses)
    (roots : G.ContinuationRootPresentation) :
    h.toFiniteObservedGame.ContinuationRootPresentation where
  IsRoot := fun history =>
    roots.IsRoot (h.originalHistory history.1)
  init_isRoot := by
    simpa using roots.init_isRoot

/-- Membership in a pulled root presentation is exactly membership of the
represented original history. -/
@[simp]
theorem pullRootPresentation_isRoot_iff
    (h : G.FiniteEFGHypotheses)
    (roots : G.ContinuationRootPresentation)
    (history : h.toFiniteObservedGame.base.History) :
    (h.pullRootPresentation roots).IsRoot history ↔
      roots.IsRoot (h.originalHistory history.1) :=
  Iff.rfl

/-- The canonical strict isomorphism exactly preserves every externally
selected root presentation pulled to the finite occurrence carrier. -/
theorem toOriginalIso_preservesRootPresentation
    (h : G.FiniteEFGHypotheses)
    (roots : G.ContinuationRootPresentation) :
    h.toOriginalIso.PreservesRootPresentations
      (h.pullRootPresentation roots) roots := by
  intro history
  rfl

/-- Pull a lawful payoff-free subgame system to the finite occurrence
presentation through the canonical strict isomorphism. -/
noncomputable def pullSubgameSystem
    (h : G.FiniteEFGHypotheses)
    (system : G.SubgameSystem) :
    h.toFiniteObservedGame.SubgameSystem :=
  h.toOriginalIso.symm.mapSubgameSystem system

/-- Pull a complete lawful payoff-free subgame system to the finite
occurrence presentation. -/
noncomputable def pullCompleteSubgameSystem
    (h : G.FiniteEFGHypotheses)
    (system : G.CompleteSubgameSystem) :
    h.toFiniteObservedGame.CompleteSubgameSystem :=
  h.toOriginalIso.symm.mapCompleteSubgameSystem system

/-- A pulled lawful system selects exactly those bounded occurrences whose
original histories were selected. -/
@[simp]
theorem pullSubgameSystem_isRoot_iff
    (h : G.FiniteEFGHypotheses)
    (system : G.SubgameSystem)
    (history : h.toFiniteObservedGame.base.History) :
    (h.pullSubgameSystem system).IsRoot history ↔
      system.IsRoot (h.originalHistory history.1) :=
  Iff.rfl

/-- Lawfulness of every selected subgame root is formally preserved by the
finite occurrence unfolding. -/
theorem pullSubgameSystem_isLawful
    (h : G.FiniteEFGHypotheses)
    (system : G.SubgameSystem)
    {history : h.toFiniteObservedGame.base.History}
    (hroot : system.IsRoot (h.originalHistory history.1)) :
    h.toFiniteObservedGame.IsLawfulSubgameRoot history :=
  (h.pullSubgameSystem system).isLawful hroot

/-- Pull a history-sensitive terminal objective back to an unfolding
endpoint without quotienting histories that share a compact state. -/
def pullTerminalOutcome
    (h : G.FiniteEFGHypotheses)
    {Outcome : Type*}
    (outcome :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (state : h.toFiniteHistoryGame.State)
    (hterminal :
      h.toFiniteHistoryGame.isTerminal state) :
    Outcome :=
  outcome ⟨h.originalHistory state, hterminal⟩

/-- Pull a discrete chance kernel through the occurrence-sensitive
unfolding. -/
def pullDiscreteChanceKernel
    (h : G.FiniteEFGHypotheses)
    (chanceKernel :
      (history : G.base.History) →
        G.base.isChanceState history.1 →
          PMF (G.base.Action history.1))
    (history : h.toFiniteObservedGame.base.History)
    (hchance :
      h.toFiniteObservedGame.base.isChanceState history.1) :
    PMF (h.toFiniteObservedGame.base.Action history.1) :=
  chanceKernel (h.originalHistory history.1) hchance

/-- Pulled discrete chance is definitionally the original law at the
represented complete history. -/
@[simp]
theorem pullDiscreteChanceKernel_eq
    (h : G.FiniteEFGHypotheses)
    (chanceKernel :
      (history : G.base.History) →
        G.base.isChanceState history.1 →
          PMF (G.base.Action history.1))
    (history : h.toFiniteObservedGame.base.History)
    (hchance :
      h.toFiniteObservedGame.base.isChanceState history.1) :
    h.pullDiscreteChanceKernel chanceKernel history hchance =
      chanceKernel (h.originalHistory history.1) hchance :=
  rfl

/-- Package the pulled PMF kernel as a discrete payoff-free chance game. -/
noncomputable def toFiniteObservedChanceGame
    (h : G.FiniteEFGHypotheses)
    (chanceKernel :
      (history : G.base.History) →
        G.base.isChanceState history.1 →
          PMF (G.base.Action history.1)) :
    DiscreteControlledObservedChanceGame N where
  observed := h.toFiniteObservedGame
  chanceKernel :=
    h.pullDiscreteChanceKernel chanceKernel

/-- Push a PMF through a carrier equivalence. -/
noncomputable def pmfEquiv
    {α β : Type*} (e : α ≃ β) :
    PMF α ≃ PMF β where
  toFun := fun law => law.map e
  invFun := fun law => law.map e.symm
  left_inv := by
    intro law
    change (law.map e).map e.symm = law
    rw [PMF.map_comp]
    rw [show (e.symm ∘ e : α → α) = id by
      funext action
      exact e.symm_apply_apply action]
    exact PMF.map_id law
  right_inv := by
    intro law
    change (law.map e.symm).map e = law
    rw [PMF.map_comp]
    rw [show (e ∘ e.symm : β → β) = id by
      funext action
      exact e.apply_symm_apply action]
    exact PMF.map_id law

/-- Behavioral contingent-plan carriers are canonically equivalent after
pulling the discrete chance law to the finite occurrence unfolding. -/
noncomputable def behavioralStrategyEquiv
    (h : G.FiniteEFGHypotheses)
    (chanceKernel :
      (history : G.base.History) →
        G.base.isChanceState history.1 →
          PMF (G.base.Action history.1))
    (i : N) :
    (h.toFiniteObservedChanceGame chanceKernel).BehavioralStrategy i ≃
      (DiscreteControlledObservedChanceGame.withChanceKernel
        G chanceKernel).BehavioralStrategy i :=
  Equiv.piCongrRight fun information =>
    pmfEquiv
      { toFun := ULift.down
        invFun := ULift.up
        left_inv := fun action => by cases action; rfl
        right_inv := fun _action => rfl }

/-- Map a finite-unfolding behavioral profile back to the original
payoff-free discrete chance presentation. -/
noncomputable def mapBehavioralProfile
    (h : G.FiniteEFGHypotheses)
    (chanceKernel :
      (history : G.base.History) →
        G.base.isChanceState history.1 →
          PMF (G.base.Action history.1))
    (profile :
      (h.toFiniteObservedChanceGame
        chanceKernel).BehavioralProfile) :
    (DiscreteControlledObservedChanceGame.withChanceKernel
      G chanceKernel).BehavioralProfile :=
  fun i => h.behavioralStrategyEquiv chanceKernel i (profile i)

/-- Behavioral profile transport commutes with unilateral deviation. -/
theorem mapBehavioralProfile_update
    [DecidableEq N]
    (h : G.FiniteEFGHypotheses)
    (chanceKernel :
      (history : G.base.History) →
        G.base.isChanceState history.1 →
          PMF (G.base.Action history.1))
    (profile :
      (h.toFiniteObservedChanceGame
        chanceKernel).BehavioralProfile)
    (who : N)
    (deviation :
      (h.toFiniteObservedChanceGame
        chanceKernel).BehavioralStrategy who) :
    h.mapBehavioralProfile chanceKernel
        (Function.update profile who deviation) =
      Function.update
        (h.mapBehavioralProfile chanceKernel profile)
        who
        (h.behavioralStrategyEquiv
          chanceKernel who deviation) := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [mapBehavioralProfile]
  · simp [mapBehavioralProfile, hi]

/-- The behavioral/chance history-policy square commutes under the canonical
strict history isomorphism of the finite occurrence unfolding. -/
theorem mapBehavioralHistoryPolicy
    (h : G.FiniteEFGHypotheses)
    (chanceKernel :
      (history : G.base.History) →
        G.base.isChanceState history.1 →
          PMF (G.base.Action history.1))
    (profile :
      (h.toFiniteObservedChanceGame
        chanceKernel).BehavioralProfile)
    (history : h.toFiniteObservedGame.base.History)
    (hsource :
      ¬ h.toFiniteObservedGame.base.isTerminal history.1)
    (htarget :
      ¬ G.base.isTerminal
        (h.toOriginalIso.historyIso.stateEquiv history).1) :
    (((profile.toHistoryPolicy
          (h.toFiniteObservedChanceGame chanceKernel))
        history hsource).map
          (h.toOriginalIso.historyIso.actionEquiv history)) =
      ((h.mapBehavioralProfile chanceKernel profile).toHistoryPolicy
          (DiscreteControlledObservedChanceGame.withChanceKernel
            G chanceKernel))
        (h.toOriginalIso.historyIso.stateEquiv history)
        htarget := by
  cases hmover :
      h.toFiniteObservedGame.base.mover history.1 with
  | some i =>
      have htargetMover :
          G.base.mover
              (h.toOriginalIso.historyIso.stateEquiv history).1 =
            some i := by
        rw [h.toOriginalIso.map_mover history]
        exact hmover
      rw [DiscreteControlledObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_mover
          (h.toFiniteObservedChanceGame chanceKernel)
          profile history hsource i hmover]
      rw [DiscreteControlledObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_mover
          (DiscreteControlledObservedChanceGame.withChanceKernel
            G chanceKernel)
          (h.mapBehavioralProfile chanceKernel profile)
          (h.toOriginalIso.historyIso.stateEquiv history)
          htarget i htargetMover]
      have hmoverProof : htargetMover = hmover :=
        Subsingleton.elim _ _
      cases hmoverProof
      unfold
        DiscreteControlledObservedChanceGame.BehavioralStrategy.actionLawAt
      change
        ((profile i
            (G.infoAt
              (h.originalHistory history.1) i hmover)).map
          (fun action =>
            G.actionEquiv
              (h.originalHistory history.1)
              i hmover action.down)).map id =
          ((profile i
              (G.infoAt
                (h.originalHistory history.1) i hmover)).map
            ULift.down).map
              (G.actionEquiv
                (h.originalHistory history.1) i hmover)
      rw [PMF.map_id, PMF.map_comp]
      rfl
  | none =>
      have htargetMover :
          G.base.mover
              (h.toOriginalIso.historyIso.stateEquiv history).1 =
            none := by
        rw [h.toOriginalIso.map_mover history]
        exact hmover
      rw [DiscreteControlledObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_chance
          (h.toFiniteObservedChanceGame chanceKernel)
          profile history hsource hmover]
      rw [DiscreteControlledObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_chance
          (DiscreteControlledObservedChanceGame.withChanceKernel
            G chanceKernel)
          (h.mapBehavioralProfile chanceKernel profile)
          (h.toOriginalIso.historyIso.stateEquiv history)
          htarget htargetMover]
      simpa [toFiniteObservedChanceGame,
        pullDiscreteChanceKernel, toOriginalIso,
        historyArenaIso] using
        PMF.map_id
          (chanceKernel
            (h.originalHistory history.1)
            ⟨hmover, hsource⟩)

/-- Complete bounded history execution law is preserved by finite occurrence
unfolding for every behavioral profile, initial history, and fuel. -/
theorem mapBehavioralHistoryLaw
    (h : G.FiniteEFGHypotheses)
    [(state : h.toFiniteObservedGame.base.State) →
      Decidable
        (h.toFiniteObservedGame.base.isTerminal state)]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (chanceKernel :
      (history : G.base.History) →
        G.base.isChanceState history.1 →
          PMF (G.base.Action history.1))
    (profile :
      (h.toFiniteObservedChanceGame
        chanceKernel).BehavioralProfile)
    (current : h.toFiniteObservedGame.base.History)
    (fuel : ℕ) :
    ((h.toFiniteObservedGame.base.toArena.stochasticHistoryPMFFrom
          (DiscreteControlledObservedChanceGame.BehavioralProfile.toHistoryPolicy
            (h.toFiniteObservedChanceGame chanceKernel) profile)
          current fuel).map
        h.toOriginalIso.historyIso.stateEquiv) =
      G.base.toArena.stochasticHistoryPMFFrom
        (DiscreteControlledObservedChanceGame.BehavioralProfile.toHistoryPolicy
          (DiscreteControlledObservedChanceGame.withChanceKernel
            G chanceKernel)
          (h.mapBehavioralProfile chanceKernel profile))
        (h.toOriginalIso.historyIso.stateEquiv current)
        fuel :=
  ExtensiveGame.Arena.Iso.map_stochasticHistoryPMFFrom
    h.toOriginalIso.historyIso
    (DiscreteControlledObservedChanceGame.BehavioralProfile.toHistoryPolicy
      (h.toFiniteObservedChanceGame chanceKernel) profile)
    (DiscreteControlledObservedChanceGame.BehavioralProfile.toHistoryPolicy
      (DiscreteControlledObservedChanceGame.withChanceKernel
        G chanceKernel)
      (h.mapBehavioralProfile chanceKernel profile))
    (h.mapBehavioralHistoryPolicy chanceKernel profile)
    current fuel

/-- The finite occurrence unfolding packages its exact bounded-history PMF
theorem as a genuine cross-representation preservation certificate. -/
noncomputable def boundedHistoryLawPreservation
    (h : G.FiniteEFGHypotheses)
    [finiteTerminalDecidable :
      (state : h.toFiniteObservedGame.base.State) →
      Decidable
        (h.toFiniteObservedGame.base.isTerminal state)]
    [originalTerminalDecidable :
      (state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (chanceKernel :
      (history : G.base.History) →
        G.base.isChanceState history.1 →
          PMF (G.base.Action history.1)) :
    DiscreteControlledObservedChanceGame.CrossGameBoundedCompleteHistoryLawRealization
      ((@DiscreteControlledObservedChanceGame.behavioralCertifiedExecutionLaw
          _ (h.toFiniteObservedChanceGame chanceKernel)
          finiteTerminalDecidable).toBoundedHistoryLawFamily)
      ((@DiscreteControlledObservedChanceGame.behavioralCertifiedExecutionLaw
          _ (DiscreteControlledObservedChanceGame.withChanceKernel
            G chanceKernel)
          originalTerminalDecidable).toBoundedHistoryLawFamily) where
  mapStrategy := fun i =>
    h.behavioralStrategyEquiv chanceKernel i
  mapHistory :=
    h.toOriginalIso.historyIso.stateEquiv
  historyLaw_map_eq := by
    intro profile current fuel
    exact
      h.mapBehavioralHistoryLaw
        chanceKernel profile current fuel

/-- The payoff-free finite unfolding retains the declared length bound. -/
theorem toFiniteHistoryGame_hasLengthBound
    (h : G.FiniteEFGHypotheses) :
    h.toFiniteHistoryGame.toArena.HasLengthBoundFrom
      h.toFiniteHistoryGame.init h.lengthBound :=
  Arena.boundedUnfolding_hasLengthBoundFrom h.hasLengthBound

/-- Distinct original histories remain distinct unfolding states, including
histories that merge at a common compact endpoint. -/
theorem state_ne_of_originalHistory_ne
    (h : G.FiniteEFGHypotheses)
    {first second : h.toFiniteHistoryGame.State}
    (hne :
      h.originalHistory first ≠
        h.originalHistory second) :
    first ≠ second := by
  intro heq
  exact hne (congrArg h.originalHistory heq)

end ExtensiveGame.ControlledObservedGame.FiniteEFGHypotheses
