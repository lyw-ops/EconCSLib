/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Compiler.FiniteImperfectObserved
import Lean.Elab.Tactic.Omega

/-!
# Finite imperfect-information compilation

This example keeps the compact tiny-game data, its observed-EFG compiler, and
the perfect-recall regression outside the reusable frontend and compiler
modules.
-/

namespace Examples.ImperfectInformation

open FiniteImperfectGame

inductive Player | P0 | P1
  deriving DecidableEq

inductive State | root | left | right | stop
  deriving DecidableEq

instance : Fintype State :=
  ⟨⟨[State.root, State.left, State.right, State.stop], by decide⟩,
    fun x => by cases x <;> decide⟩

inductive Info | hiddenChoice
  deriving DecidableEq

inductive RootAction | L | R
  deriving DecidableEq

inductive P1Action | Stop
  deriving DecidableEq

/-- A tiny imperfect-information game where player 1 cannot distinguish two
singleton-action states reached after player 0's root choice. -/
def tiny : FiniteImperfectGame Player ℤ where
  State := State
  InfoSet := Info
  InfoAction
    | .hiddenChoice => P1Action
  Action
    | .root => RootAction
    | .left => P1Action
    | .right => P1Action
    | .stop => PEmpty
  next
    | .root, RootAction.L => .left
    | .root, RootAction.R => .right
    | .left, P1Action.Stop => .stop
    | .right, P1Action.Stop => .stop
  init := .root
  mover
    | .root => some .P0
    | .left => some .P1
    | .right => some .P1
    | .stop => none
  info
    | .left => some .hiddenChoice
    | .right => some .hiddenChoice
    | _ => none
  actionEquiv
    | .left, .hiddenChoice, _ => Equiv.refl P1Action
    | .right, .hiddenChoice, _ => Equiv.refl P1Action
    | .root, .hiddenChoice, h => by simp at h
    | .stop, .hiddenChoice, h => by simp at h
  payoff _ _ := 0

theorem tiny_same_mover : tiny.SameMoverOnInfo := by
  intro s t k hs ht
  cases s <;> cases t <;> cases k <;> simp [tiny] at hs ht ⊢

theorem tiny_no_chance_on_info : tiny.NoChanceOnDecisionInfo := by
  intro s k hs
  cases s <;> cases k <;> simp [tiny] at hs ⊢

/-- The two nodes in the hidden information set expose equivalent action
types. -/
theorem tiny_same_actions : tiny.SameActionsOnInfo := by
  exact tiny.sameActionsOnInfo

/-- The tiny compact game satisfies the compiler's local information
well-formedness obligations. -/
theorem tiny_infoWellFormed : tiny.InfoWellFormed :=
  ⟨tiny_same_mover,
    tiny_no_chance_on_info⟩

/-- Conservative observed-EFG compiler certificate for the tiny game. -/
def tinyObservedCompiler : tiny.ObservedCompiler :=
  ObservedCompiler.ofInfoWellFormed
    tiny_infoWellFormed

/-- The tiny finite imperfect game compiled to the canonical observed-EFG
interface. -/
noncomputable def tinyObservedGame :
    ExtensiveGame.ObservedGame Player ℤ :=
  tinyObservedCompiler.toObservedGame

/-- Complete history reaching the left hidden node. -/
def tinyLeftHistory :
    tiny.toExtensiveGame.toArena.HistoryFrom
      tiny.toExtensiveGame.init :=
  ⟨State.left,
    (Arena.History.nil :
      tiny.toExtensiveGame.toArena.History
        tiny.toExtensiveGame.init
        tiny.toExtensiveGame.init).snoc RootAction.L⟩

/-- Complete history reaching the right hidden node. -/
def tinyRightHistory :
    tiny.toExtensiveGame.toArena.HistoryFrom
      tiny.toExtensiveGame.init :=
  ⟨State.right,
    (Arena.History.nil :
      tiny.toExtensiveGame.toArena.History
        tiny.toExtensiveGame.init
        tiny.toExtensiveGame.init).snoc RootAction.R⟩

/-- Player 1 moves at the left hidden history. -/
theorem tinyLeftHistory_mover :
    tinyObservedGame.base.mover tinyLeftHistory.1 =
      some Player.P1 := by
  rfl

/-- Player 1 moves at the right hidden history. -/
theorem tinyRightHistory_mover :
    tinyObservedGame.base.mover tinyRightHistory.1 =
      some Player.P1 := by
  rfl

/-- The left hidden history admits the `Stop` action. -/
theorem tinyLeftHistory_nonterminal :
    ¬ tinyObservedGame.base.isTerminal tinyLeftHistory.1 :=
  fun hterminal => hterminal.false P1Action.Stop

/-- The right hidden history admits the `Stop` action. -/
theorem tinyRightHistory_nonterminal :
    ¬ tinyObservedGame.base.isTerminal tinyRightHistory.1 :=
  fun hterminal => hterminal.false P1Action.Stop

/-- The compiler actually identifies the left and right player-1 decisions as
one information state. -/
theorem tinyObserved_infoAt_left_right :
    tinyObservedGame.infoAt
        tinyLeftHistory Player.P1 tinyLeftHistory_mover
          tinyLeftHistory_nonterminal =
      tinyObservedGame.infoAt
        tinyRightHistory Player.P1 tinyRightHistory_mover
          tinyRightHistory_nonterminal :=
  tiny.decisionInfoAt_eq_of_same_info
    State.left State.right Player.P1
    tinyLeftHistory_mover tinyRightHistory_mover
    Info.hiddenChoice rfl rfl

/-- Consequently every compiled pure profile makes the same packaged abstract
choice at the two hidden nodes. -/
theorem tinyObserved_choice_left_right
    (profile : tinyObservedGame.PureProfile) :
    (⟨tinyObservedGame.infoAt
          tinyLeftHistory Player.P1 tinyLeftHistory_mover
            tinyLeftHistory_nonterminal,
        profile Player.P1
          (tinyObservedGame.infoAt
            tinyLeftHistory Player.P1 tinyLeftHistory_mover
              tinyLeftHistory_nonterminal)⟩ :
      Σ information : tinyObservedGame.InfoState Player.P1,
        tinyObservedGame.InfoAction Player.P1 information) =
    ⟨tinyObservedGame.infoAt
        tinyRightHistory Player.P1 tinyRightHistory_mover
          tinyRightHistory_nonterminal,
      profile Player.P1
        (tinyObservedGame.infoAt
          tinyRightHistory Player.P1 tinyRightHistory_mover
            tinyRightHistory_nonterminal)⟩ :=
  profile.choice_eq_of_infoState_eq
    tinyObservedGame Player.P1
    tinyLeftHistory tinyRightHistory
    tinyLeftHistory_mover tinyRightHistory_mover
    tinyLeftHistory_nonterminal tinyRightHistory_nonterminal
    tinyObserved_infoAt_left_right

/-- Remaining decision depth of a compact tiny-game state. -/
def tinyDecisionRank : State → ℕ
  | .root => 2
  | .left | .right => 1
  | .stop => 0

/-- Every tiny-game action consumes exactly one unit of decision depth. -/
theorem tinyDecisionRank_next
    (state : State) (action : tiny.Action state) :
    tinyDecisionRank (tiny.next state action) + 1 =
      tinyDecisionRank state := by
  cases state <;> cases action <;> rfl

/-- A complete tiny-game history partitions the initial decision depth into
elapsed actions and remaining depth. -/
theorem tinyHistory_length_add_rank
    {state : State}
    (path :
      tiny.toExtensiveGame.toArena.History
        tiny.toExtensiveGame.init state) :
    path.length + tinyDecisionRank state = 2 := by
  refine
    Arena.History.rec
      (motive := fun state path =>
        path.length + tinyDecisionRank state = 2)
      ?_ ?_ path
  · rfl
  · intro state path action ih
    rw [Arena.History.length_snoc]
    change
      (path.length + 1) +
          tinyDecisionRank (tiny.next state action) =
        2
    have hstep := tinyDecisionRank_next state action
    omega

/-- A player-controlled tiny-game state has positive remaining decision
depth. -/
theorem tinyDecisionRank_pos_of_mover
    {state : State} {i : Player}
    (hmover : tiny.mover state = some i) :
    0 < tinyDecisionRank state := by
  cases state <;> cases i <;> simp [tiny, tinyDecisionRank] at hmover ⊢

/-- Every decision in the tiny game is the acting player's first decision. -/
theorem tinyObserved_ownDecisionHistory_eq_nil
    (i : Player)
    (history :
      tinyObservedGame.base.toArena.HistoryFrom
        tinyObservedGame.base.init)
    (hmover :
      tinyObservedGame.base.mover history.1 = some i) :
    tinyObservedGame.ownDecisionHistory i history = [] := by
  obtain ⟨state, path⟩ := history
  have hlength := tinyHistory_length_add_rank path
  have hrank :
      0 < tinyDecisionRank state := by
    apply tinyDecisionRank_pos_of_mover
    exact hmover
  cases path with
  | nil =>
      rfl
  | @snoc previous path action =>
      cases path with
      | nil =>
          cases action <;> cases i <;>
            simp [ExtensiveGame.ObservedGame.ownDecisionHistory,
              ExtensiveGame.ControlledObservedGame.ownDecisionHistory,
              ExtensiveGame.ControlledObservedGame.ownDecisionHistoryPath,
              tinyObservedGame,
              FiniteImperfectGame.ObservedCompiler.toObservedGame,
              FiniteImperfectGame.toExtensiveGame, tiny] at hmover ⊢
      | @snoc earlier earlierPath earlierAction =>
          simp [Arena.History.length] at hlength
          omega

/-- A factorization certificate for perfect recall in the compiled tiny
imperfect-information game. -/
noncomputable def tinyObservedRecallCertificate :
    tinyObservedGame.RecallCertificate where
  remembered := fun _ _ => []
  remembered_infoAt := by
    intro i history hmover _hnonterminal
    exact
      (tinyObserved_ownDecisionHistory_eq_nil
        i history hmover).symm

/-- The compiled tiny imperfect-information game has perfect recall even
though player 1's current information state merges two distinct histories. -/
theorem tinyObserved_perfectRecall :
    tinyObservedGame.PerfectRecall :=
  tinyObservedRecallCertificate.perfectRecall

end Examples.ImperfectInformation
