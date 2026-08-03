/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Finite
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Recall
import EconCSLib.GameTheory.ExtensiveGame.Winning.Basic

/-!
# Logical determinacy interfaces

Determinacy is a solution concept, not a property of a winning-set family by
definition. This module therefore keeps `IsTotal`, `IsTwoPlayerZeroSum`, and
`IsTwoPlayerDetermined` separate. For arbitrary player types, the weaker
descriptive predicate is named `HasSomePathwiseWinningStrategy`; calling it
determinacy would blur the standard two-player logical-game meaning.

`FiniteTwoPlayerHypotheses` records the structural assumptions for finite
backward determinacy without baking them into `ObservedGame` or
`WinningCondition`. The theorem below constructs an information-consistent
strategy; it does not replace observed strategies by history-indexed policies.

The payoff-free carrier owns the logical predicates. This module proves both
the exclusivity boundary (two robust winners cannot coexist) and genuine
finite perfect-information determinacy by well-founded backward recursion.
Well-founded prefix and topological determinacy remain separate theorem
tracks; existence is never inferred from totality alone.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*} {G : ControlledObservedGame N}

/-- Pathwise winning strategies for one player in a payoff-free observed
game, bundled with their robust winning proof. -/
abbrev PathwiseWinningStrategies
    (G : ControlledObservedGame N)
    (W : G.base.WinningCondition)
    (i : N) :=
  {strategy : G.PureStrategy i //
    G.HasPathwiseWinningStrategy W i strategy}

/-- Some player has a robust pure pathwise winning strategy. -/
def HasSomePathwiseWinningStrategy
    (G : ControlledObservedGame N)
    (W : G.base.WinningCondition) : Prop :=
  ∃ (i : N) (strategy : G.PureStrategy i),
    G.HasPathwiseWinningStrategy W i strategy

/-- Constructive two-player determinacy on the payoff-free carrier. -/
def IsTwoPlayerDetermined
    (G : ControlledObservedGame (Fin 2))
    (W : G.base.WinningCondition) : Prop :=
  (∃ strategy : G.PureStrategy 0,
      G.HasPathwiseWinningStrategy W 0 strategy) ∨
    (∃ strategy : G.PureStrategy 1,
      G.HasPathwiseWinningStrategy W 1 strategy)

/-- For two players, existence of some pathwise winner is the explicit
determinacy disjunction. -/
theorem hasSomePathwiseWinningStrategy_iff_isTwoPlayerDetermined
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition} :
    G.HasSomePathwiseWinningStrategy W ↔
      G.IsTwoPlayerDetermined W := by
  constructor
  · rintro ⟨i, strategy, hwinning⟩
    fin_cases i
    · exact Or.inl ⟨strategy, hwinning⟩
    · exact Or.inr ⟨strategy, hwinning⟩
  · rintro (hzero | hone)
    · rcases hzero with ⟨strategy, hwinning⟩
      exact ⟨0, strategy, hwinning⟩
    · rcases hone with ⟨strategy, hwinning⟩
      exact ⟨1, strategy, hwinning⟩

/-- Structural assumptions for finite perfect-information payoff-free
determinacy. -/
structure FiniteTwoPlayerHypotheses
    (G : ControlledObservedGame (Fin 2))
    (W : G.base.WinningCondition) : Type _ where
  /-- The reachable complete-history unfolding is uniformly finite. -/
  finiteEFG : G.FiniteEFGHypotheses
  /-- Every nonterminal history is player controlled. -/
  noChance : G.base.NoChanceOnHistories
  /-- Decision information determines the complete history. -/
  perfectInformation : G.PerfectInformation
  /-- Exactly one player wins each complete play. -/
  zeroSum : W.IsTwoPlayerZeroSum

/-! ### Finite perfect-information backward induction -/

/-- The other member of `Fin 2`. -/
def otherPlayer (i : Fin 2) : Fin 2 :=
  if i = 0 then 1 else 0

@[simp]
theorem otherPlayer_zero : otherPlayer 0 = 1 := by
  simp [otherPlayer]

@[simp]
theorem otherPlayer_one : otherPlayer 1 = 0 := by
  simp [otherPlayer]

theorem otherPlayer_ne (i : Fin 2) :
    otherPlayer i ≠ i := by
  fin_cases i <;> simp

theorem eq_otherPlayer_of_ne {i j : Fin 2}
    (hne : j ≠ i) :
    j = otherPlayer i := by
  fin_cases i <;> fin_cases j <;> simp_all

/-- The canonical root play obtained by replaying one terminal complete
history and then stuttering forever. -/
def terminalReplay
    (G : ControlledObservedGame (Fin 2))
    (history : G.base.History)
    (hterminal : G.base.isTerminal history.1) :
    G.base.CompletePlay :=
  Arena.CompletePlayFromHistory.prependHistory history.2
    (Arena.CompletePlayFromHistory.stutter history hterminal)

/-- The unique winner assigned by a total two-player objective to a canonical
terminal replay. -/
noncomputable def terminalWinner
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (hzeroSum : W.IsTwoPlayerZeroSum)
    (history : G.base.History)
    (hterminal : G.base.isTerminal history.1) :
    Fin 2 :=
  Classical.choose
    (hzeroSum.isTotal (terminalReplay G history hterminal))

/-- The terminal winner really wins the canonical replay used to define it.
-/
theorem terminalReplay_mem_terminalWinner
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (hzeroSum : W.IsTwoPlayerZeroSum)
    (history : G.base.History)
    (hterminal : G.base.isTerminal history.1) :
    terminalReplay G history hterminal ∈
      W (terminalWinner hzeroSum history hterminal) :=
  Classical.choose_spec
    (hzeroSum.isTotal (terminalReplay G history hterminal))

/-- Backward-induction winner of every complete history.

At a decision history, the mover wins exactly when some child is winning for
that mover; otherwise the other player wins. At terminal histories the winner
is read from the arbitrary path objective on the canonical terminal replay.
-/
noncomputable def backwardWinner
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W) :
    G.base.History → Fin 2 :=
  by
    classical
    exact
      @WellFounded.fix G.base.History (fun _ => Fin 2)
        (G.base.toArena.IsChildFrom
          (start := G.base.init))
        h.finiteEFG.isWellFoundedFrom.wellFounded_isChildFrom
        (fun history recurse =>
          if hterminal : G.base.isTerminal history.1 then
            terminalWinner h.zeroSum history hterminal
          else
            let mover :=
              Classical.choose
                (h.noChance history hterminal)
            if ∃ action : G.base.Action history.1,
                recurse
                    ⟨G.base.next history.1 action,
                      history.2.snoc action⟩
                    (Arena.IsChildFrom.snoc history action) =
                  mover then
              mover
            else
              otherPlayer mover)

/-- Unfold one step of the finite backward-winner recursion. -/
theorem backwardWinner_eq
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W)
    (history : G.base.History) :
    backwardWinner h history =
      (by
        classical
        exact
          if hterminal : G.base.isTerminal history.1 then
            terminalWinner h.zeroSum history hterminal
          else
            let mover :=
              Classical.choose
                (h.noChance history hterminal)
            if ∃ action : G.base.Action history.1,
                backwardWinner h
                    ⟨G.base.next history.1 action,
                      history.2.snoc action⟩ =
                  mover then
              mover
            else
              otherPlayer mover) := by
  classical
  unfold backwardWinner
  rw [WellFounded.fix_eq]

/-- At a terminal history, backward induction agrees with the objective's
winner of the canonical terminal replay. -/
theorem backwardWinner_eq_of_terminal
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W)
    (history : G.base.History)
    (hterminal : G.base.isTerminal history.1) :
    backwardWinner h history =
      terminalWinner h.zeroSum history hterminal := by
  classical
  rw [backwardWinner_eq]
  simp [hterminal]

/-- When the current mover is the backward winner, some legal action keeps
the same backward winner at the child. -/
theorem exists_action_backwardWinner_eq
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W)
    (history : G.base.History)
    (hmover :
      G.base.mover history.1 =
        some (backwardWinner h history)) :
    ∃ action : G.base.Action history.1,
      backwardWinner h
          ⟨G.base.next history.1 action,
            history.2.snoc action⟩ =
        backwardWinner h history := by
  classical
  have hnonterminal :
      ¬ G.base.isTerminal history.1 := by
    intro hterminal
    rcases
        h.finiteEFG.decisionMoverCoherent history
          (backwardWinner h history) hmover with
      ⟨action⟩
    exact hterminal.false action
  let mover :=
    Classical.choose
      (h.noChance history hnonterminal)
  have hmoverChosen :
      G.base.mover history.1 = some mover :=
    Classical.choose_spec
      (h.noChance history hnonterminal)
  have hmover_eq :
      mover = backwardWinner h history :=
    Option.some.inj (hmoverChosen.symm.trans hmover)
  have hexists :
      ∃ action : G.base.Action history.1,
        backwardWinner h
            ⟨G.base.next history.1 action,
              history.2.snoc action⟩ =
          mover := by
    by_contra hnone
    have hwinner := backwardWinner_eq h history
    simp [hnonterminal, mover, hnone] at hwinner
    exact
      (otherPlayer_ne mover)
        ((hmover_eq.trans hwinner).symm)
  rcases hexists with ⟨action, haction⟩
  exact ⟨action, haction.trans hmover_eq⟩

/-- At a node controlled by the player other than its backward winner, every
legal action keeps the same backward winner. -/
theorem backwardWinner_child_eq_of_ne
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W)
    (history : G.base.History)
    (i : Fin 2)
    (hmover : G.base.mover history.1 = some i)
    (hne : i ≠ backwardWinner h history)
    (action : G.base.Action history.1) :
    backwardWinner h
        ⟨G.base.next history.1 action,
          history.2.snoc action⟩ =
      backwardWinner h history := by
  classical
  have hnonterminal :
      ¬ G.base.isTerminal history.1 :=
    fun hterminal => hterminal.false action
  let mover :=
    Classical.choose
      (h.noChance history hnonterminal)
  have hmoverChosen :
      G.base.mover history.1 = some mover :=
    Classical.choose_spec
      (h.noChance history hnonterminal)
  have hmover_eq : mover = i :=
    Option.some.inj (hmoverChosen.symm.trans hmover)
  by_cases hexists :
      ∃ nextAction : G.base.Action history.1,
        backwardWinner h
            ⟨G.base.next history.1 nextAction,
              history.2.snoc nextAction⟩ =
          mover
  · have hwinner := backwardWinner_eq h history
    simp [hnonterminal, mover, hexists] at hwinner
    exact
      (hne (hmover_eq.symm.trans hwinner.symm)).elim
  · have hchild_ne :
        backwardWinner h
            ⟨G.base.next history.1 action,
              history.2.snoc action⟩ ≠
          mover := by
      intro heq
      exact hexists ⟨action, heq⟩
    have hchild_other :=
      eq_otherPlayer_of_ne hchild_ne
    have hwinner := backwardWinner_eq h history
    simp [hnonterminal, mover, hexists] at hwinner
    exact hchild_other.trans hwinner.symm

/-- The concrete child selected at a node won by its mover. -/
noncomputable def backwardAction
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W)
    (history : G.base.History)
    (hmover :
      G.base.mover history.1 =
        some (backwardWinner h history)) :
    G.base.Action history.1 :=
  Classical.choose
    (exists_action_backwardWinner_eq h history hmover)

/-- The selected backward action preserves the winner. -/
theorem backwardWinner_backwardAction
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W)
    (history : G.base.History)
    (hmover :
      G.base.mover history.1 =
        some (backwardWinner h history)) :
    backwardWinner h
        ⟨G.base.next history.1
            (backwardAction h history hmover),
          history.2.snoc
            (backwardAction h history hmover)⟩ =
      backwardWinner h history :=
  Classical.choose_spec
    (exists_action_backwardWinner_eq h history hmover)

/-- Transporting an abstract action from an equal representative history and
then realizing it returns the representative's concrete action, up to the
dependent action-fiber equality induced by the history equality. -/
theorem actionEquiv_transport_symm_heq
    {G : ControlledObservedGame (Fin 2)}
    {i : Fin 2}
    (first second : G.base.History)
    (hfirst : G.base.mover first.1 = some i)
    (hsecond : G.base.mover second.1 = some i)
    (hhistory : first = second)
    (hinfo :
      G.infoAt second i hsecond =
        G.infoAt first i hfirst)
    (action : G.base.Action second.1) :
    HEq
      (G.actionEquiv first i hfirst
        (hinfo ▸
          (G.actionEquiv second i hsecond).symm action))
      action := by
  subst second
  simp

/-- Equal complete histories and heterogeneously equal concrete actions
produce equal one-step child histories. -/
theorem childHistory_eq_of_heq
    {G : ControlledObservedGame (Fin 2)}
    (first second : G.base.History)
    (hhistory : first = second)
    (firstAction : G.base.Action first.1)
    (secondAction : G.base.Action second.1)
    (haction : HEq firstAction secondAction) :
    (⟨G.base.next first.1 firstAction,
        first.2.snoc firstAction⟩ :
        G.base.History) =
      ⟨G.base.next second.1 secondAction,
        second.2.snoc secondAction⟩ := by
  subst second
  have heq : firstAction = secondAction :=
    eq_of_heq haction
  subst secondAction
  rfl

/-- A chosen concrete representative of each declared decision-information
state. -/
noncomputable def backwardRepresentative
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W)
    (i : Fin 2) (information : G.InfoState i) :
    G.DecisionInfoWitness i information :=
  Classical.choice
    (h.finiteEFG.allDecisionInfoRepresented i information)

/-- The information-consistent pure strategy extracted by backward induction.

At information states in the winning region it transports the selected
concrete backward action through `actionEquiv`. Off the winning region its
value is arbitrary; those coordinates cannot be reached while the invariant
that the root winner is preserved holds. -/
noncomputable def backwardStrategy
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W) :
    G.PureStrategy
      (backwardWinner h
        (Arena.HistoryFrom.nil
          G.base.toArena G.base.init)) :=
  by
    classical
    let rootWinner :=
      backwardWinner h
        (Arena.HistoryFrom.nil
          G.base.toArena G.base.init)
    intro information
    let witness :=
      backwardRepresentative h rootWinner information
    if hinvariant :
        backwardWinner h witness.history = rootWinner then
      change G.InfoAction rootWinner information
      exact
        witness.infoAt_eq ▸
          (G.actionEquiv witness.history rootWinner
              witness.mover).symm
            (backwardAction h witness.history
              (witness.mover.trans
                (congrArg some hinvariant.symm)))
    else
      exact
        Classical.choice
          (AllDecisionInfoRepresented.nonempty_infoAction
            h.finiteEFG.allDecisionInfoRepresented
            h.finiteEFG.decisionMoverCoherent
            rootWinner information)

/-- Along the root winner's extracted strategy, a decision by that player
keeps the backward winner invariant. Singleton information is the step that
turns the representative-indexed action into the action at the actual
history. -/
theorem backwardWinner_child_of_backwardStrategy
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W)
    (history : G.base.History)
    (hmover :
      G.base.mover history.1 =
        some
          (backwardWinner h
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init)))
    (hinvariant :
      backwardWinner h history =
        backwardWinner h
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init)) :
    backwardWinner h
        ⟨G.base.next history.1
            ((backwardStrategy h).actionAt
              G history hmover),
          history.2.snoc
            ((backwardStrategy h).actionAt
              G history hmover)⟩ =
      backwardWinner h
        (Arena.HistoryFrom.nil
          G.base.toArena G.base.init) := by
  classical
  let rootWinner :=
    backwardWinner h
      (Arena.HistoryFrom.nil
        G.base.toArena G.base.init)
  let information :=
    G.infoAt history rootWinner hmover
  let witness :=
    backwardRepresentative h rootWinner information
  have hhistory : history = witness.history := by
    apply h.perfectInformation rootWinner
      history witness.history hmover witness.mover
    exact witness.infoAt_eq.symm
  have hwitness :
      backwardWinner h witness.history = rootWinner := by
    rw [← hhistory]
    simpa [rootWinner] using hinvariant
  let witnessWinnerMover :
      G.base.mover witness.history.1 =
        some (backwardWinner h witness.history) :=
    witness.mover.trans
      (congrArg some hwitness.symm)
  have hstrategyInformation :
      backwardStrategy h information =
        (witness.infoAt_eq ▸
          (G.actionEquiv witness.history rootWinner
              witness.mover).symm
            (backwardAction h witness.history
              (witness.mover.trans
                (congrArg some hwitness.symm)))) := by
    simp [backwardStrategy, rootWinner, information,
      witness, hwitness]
  have hinfo :
      G.infoAt witness.history rootWinner witness.mover =
        G.infoAt history rootWinner hmover := by
    simpa [information] using witness.infoAt_eq
  have haction :
      HEq
        ((backwardStrategy h).actionAt
          G history hmover)
        (backwardAction h witness.history
          witnessWinnerMover) := by
    change
      HEq
        (G.actionEquiv history rootWinner hmover
          (backwardStrategy h information))
        (backwardAction h witness.history
          witnessWinnerMover)
    rw [hstrategyInformation]
    exact actionEquiv_transport_symm_heq
      history witness.history hmover witness.mover
        hhistory hinfo
        (backwardAction h witness.history
          witnessWinnerMover)
  have hchild :
      (⟨G.base.next history.1
            ((backwardStrategy h).actionAt
              G history hmover),
          history.2.snoc
            ((backwardStrategy h).actionAt
              G history hmover)⟩ :
          G.base.History) =
        ⟨G.base.next witness.history.1
            (backwardAction h witness.history
              witnessWinnerMover),
          witness.history.2.snoc
            (backwardAction h witness.history
              witnessWinnerMover)⟩ :=
    childHistory_eq_of_heq
      history witness.history hhistory
      ((backwardStrategy h).actionAt
        G history hmover)
      (backwardAction h witness.history
        witnessWinnerMover)
      haction
  rw [hchild]
  have hselected :=
    backwardWinner_backwardAction
      h witness.history witnessWinnerMover
  exact hselected.trans hwitness

/-- Every play compatible with the extracted strategy stays inside the root
winner's backward-winning region at every coordinate. -/
theorem backwardWinner_historyAt_eq_root
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W)
    (play : G.base.CompletePlay)
    (hcompatible :
      G.IsCompatibleWithPlayerStrategy
        (backwardWinner h
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init))
        (backwardStrategy h) play) :
    ∀ n,
      backwardWinner h (play.historyAt n) =
        backwardWinner h
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init)
  | 0 => by
      rw [play.historyAt_zero]
  | n + 1 => by
      have ih :=
        backwardWinner_historyAt_eq_root
          h play hcompatible n
      by_cases hterminal :
          G.base.isTerminal (play.historyAt n).1
      · rw [play.at_succ_eq_of_terminal n hterminal]
        exact ih
      · rcases
          h.noChance (play.historyAt n) hterminal with
        ⟨i, hmover⟩
        by_cases hi :
            i =
              backwardWinner h
                (Arena.HistoryFrom.nil
                  G.base.toArena G.base.init)
        · subst i
          rw [hcompatible n hterminal hmover]
          exact
            backwardWinner_child_of_backwardStrategy
              h (play.historyAt n) hmover ih
        · have hne :
              i ≠ backwardWinner h (play.historyAt n) := by
            intro heq
            exact hi (heq.trans ih)
          rcases
              play.isChild_at_succ_of_not_terminal
                n hterminal with
            ⟨action, hnext⟩
          rw [hnext]
          exact
            (backwardWinner_child_eq_of_ne
              h (play.historyAt n) i hmover hne
                action).trans ih

/-- The backward-induction strategy is pathwise winning for the winner of the
root history. -/
theorem backwardStrategy_hasPathwiseWinningStrategy
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W) :
    G.HasPathwiseWinningStrategy W
      (backwardWinner h
        (Arena.HistoryFrom.nil
          G.base.toArena G.base.init))
      (backwardStrategy h) := by
  intro play hcompatible
  let bound := h.finiteEFG.lengthBound
  have hterminal :
      G.base.isTerminal (play.historyAt bound).1 :=
    Arena.HasLengthBoundAt.terminal_historyAt
      h.finiteEFG.hasLengthBound play
  have hinvariant :
      backwardWinner h (play.historyAt bound) =
        backwardWinner h
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init) :=
    backwardWinner_historyAt_eq_root
      h play hcompatible bound
  have hterminalWinner :
      terminalWinner h.zeroSum
          (play.historyAt bound) hterminal =
        backwardWinner h
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init) :=
    (backwardWinner_eq_of_terminal
      h (play.historyAt bound) hterminal).symm.trans
        hinvariant
  have hwins :=
    terminalReplay_mem_terminalWinner
      h.zeroSum (play.historyAt bound) hterminal
  have hreplay :
      terminalReplay G (play.historyAt bound) hterminal =
        play := by
    exact
      play.prependHistory_stutter_eq_of_terminal
        bound hterminal
  rw [hreplay, hterminalWinner] at hwins
  exact hwins

/-- Finite, no-chance, perfect-information, two-player zero-sum observed games
are determined by a pure information-consistent strategy.

The result returns an explicit winning-strategy witness in `Prop`, but the
backward winner and action selections used here are `noncomputable` and rely
on classical choice. It is therefore a classical existence theorem, not an
executable strategy-extraction result. -/
theorem FiniteTwoPlayerHypotheses.isTwoPlayerDetermined
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W) :
    G.IsTwoPlayerDetermined W := by
  let rootWinner :=
    backwardWinner h
      (Arena.HistoryFrom.nil
        G.base.toArena G.base.init)
  have hwinning :
      G.HasPathwiseWinningStrategy W rootWinner
        (backwardStrategy h) :=
    backwardStrategy_hasPathwiseWinningStrategy h
  have hpackage :
      ∃ strategy : G.PureStrategy rootWinner,
        G.HasPathwiseWinningStrategy W
          rootWinner strategy :=
    ⟨backwardStrategy h, hwinning⟩
  by_cases hzero : rootWinner = 0
  · exact Or.inl (hzero ▸ hpackage)
  · have hone : rootWinner = 1 :=
      Fin.eq_one_of_ne_zero rootWinner hzero
    exact Or.inr (hone ▸ hpackage)

/-- Structural assumptions for well-founded prefix determinacy on the
payoff-free carrier. -/
structure WellFoundedPrefixHypotheses
    (G : ControlledObservedGame (Fin 2))
    (W : G.base.WinningCondition) : Type _ where
  /-- Every legal history branch is structurally well founded. -/
  wellFounded :
    G.base.toArena.IsWellFoundedFrom G.base.init
  /-- Every nonterminal history is player controlled. -/
  noChance : G.base.NoChanceOnHistories
  /-- Decision information determines the complete history. -/
  perfectInformation : G.PerfectInformation
  /-- Exactly one player wins each complete play. -/
  zeroSum : W.IsTwoPlayerZeroSum
  /-- Every play reaches a persistent finite decision prefix. -/
  prefixDecision :
    Arena.WinningConditionFrom.PrefixDecision W

/-- In a payoff-free no-chance game with exclusive objectives, the two
players cannot both have robust pathwise winning strategies. -/
theorem not_both_havePathwiseWinningStrategy
    {G : ControlledObservedGame (Fin 2)}
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    {W : G.base.WinningCondition}
    (hNoChance : G.base.NoChanceOnHistories)
    (hexclusive : W.IsExclusive) :
    ¬ ((∃ strategy : G.PureStrategy 0,
          G.HasPathwiseWinningStrategy W 0 strategy) ∧
        (∃ strategy : G.PureStrategy 1,
          G.HasPathwiseWinningStrategy W 1 strategy)) := by
  rintro ⟨⟨strategyZero, hwinningZero⟩,
    ⟨strategyOne, hwinningOne⟩⟩
  let profile : G.PureProfile := fun i =>
    if hzero : i = 0 then
      hzero ▸ strategyZero
    else
      (Fin.eq_one_of_ne_zero i hzero) ▸ strategyOne
  have hprofileZero : profile 0 = strategyZero := by
    simp [profile]
  have hprofileOne : profile 1 = strategyOne := by
    simp [profile]
  let play : G.base.CompletePlay :=
    (profile.toHistoryPolicy hNoChance).completePlay
  have hcompatibleZero :
      G.IsCompatibleWithPlayerStrategy
        0 strategyZero play := by
    have hprofile :=
      profile.completePlay_isCompatibleWithPlayerStrategy
        hNoChance 0
    simpa [play, hprofileZero] using hprofile
  have hcompatibleOne :
      G.IsCompatibleWithPlayerStrategy
        1 strategyOne play := by
    have hprofile :=
      profile.completePlay_isCompatibleWithPlayerStrategy
        hNoChance 1
    simpa [play, hprofileOne] using hprofile
  have hwinsZero : play ∈ W 0 :=
    hwinningZero play hcompatibleZero
  have hwinsOne : play ∈ W 1 :=
    hwinningOne play hcompatibleOne
  exact Fin.zero_ne_one
    (hexclusive play hwinsZero hwinsOne)

end ExtensiveGame.ControlledObservedGame
