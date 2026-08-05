/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Countable

/-!
# Countable observed semantics with an uncountable player identifier type

This regression guards the cardinality-minimal boundary of the canonical
countable-discrete observed-chance presentation.

The ambient player type is `Unit ⊕ ℝ`, hence uncountable. Only the distinguished
left player ever moves. Every real-indexed unused player nevertheless has an
uncountable `ℝ` information fiber, and every such information point has an
uncountable `ℝ` action fiber.

Those declared points are unreachable, so the reachable player-information
carrier is still a singleton. The example obtains the canonical analytic
presentation using only the two-history and one-history-action covers and
checks exact one-step kernel compilation. This is a strict regression against
counting unused player identifiers, information points, or information
actions.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.ObservedChanceCountableSparsePlayersBoundary

open ExtensiveGame
open MeasurableKernelArena

/-- An uncountable ambient identifier type with one distinguished active
player. -/
abbrev Player := Unit ⊕ ℝ

/-- The sole player who occurs as a mover. -/
def activePlayer : Player :=
  .inl ()

/-- A one-decision game state space. -/
inductive Node
  | decision
  | terminal

/-- The decision node has one action and the terminal node has none. -/
def nodeAction : Node → Type
  | .decision => Unit
  | .terminal => Empty

/-- The unique decision action reaches the terminal node. -/
def nodeNext : (state : Node) → nodeAction state → Node
  | .decision, _ => .terminal
  | .terminal, action => nomatch action

/-- Only the distinguished left player moves. -/
def nodeMover : Node → Option Player
  | .decision => some activePlayer
  | .terminal => none

/-- The underlying one-decision extensive game. -/
def base : ExtensiveGame Player Unit where
  State := Node
  Action := nodeAction
  next := nodeNext
  init := .decision
  mover := nodeMover
  payoff := fun _ _ => ()

/-- The active player has one information point; every unused real-indexed
player has an uncountable declared information fiber. -/
def sparseInfoState : Player → Type
  | .inl _ => Unit
  | .inr _ => ℝ

/-- Every unused information point also has an uncountable declared action
fiber, despite never being queried by execution. -/
def sparseInfoAction :
    (i : Player) → sparseInfoState i → Type
  | .inl _, _ => Unit
  | .inr _, _ => ℝ

/-- Recover the unique sparse information state at any player-labelled
history. -/
def sparseInformationAt
    (history : base.toArena.HistoryFrom base.init)
    (i : Player)
    (hmover : base.mover history.1 = some i)
    (_hnonterminal : ¬ base.isTerminal history.1) :
    sparseInfoState i := by
  change nodeMover history.1 = some i at hmover
  cases hstate : history.1 with
  | decision =>
      rw [hstate] at hmover
      simp only [nodeMover, Option.some.injEq] at hmover
      subst i
      exact ()
  | terminal =>
      rw [hstate] at hmover
      exact (Option.some_ne_none i hmover.symm).elim

/-- The sparse abstract action is exactly the unique legal concrete action at
the only player-controlled history. -/
def sparseActionEquiv
    (history : base.toArena.HistoryFrom base.init)
    (i : Player)
    (hmover : base.mover history.1 = some i)
    (hnonterminal : ¬ base.isTerminal history.1) :
    sparseInfoAction i
        (sparseInformationAt history i hmover hnonterminal) ≃
      base.Action history.1 := by
  change nodeMover history.1 = some i at hmover
  cases hstate : history.1 with
  | decision =>
      rw [hstate] at hmover
      simp only [nodeMover, Option.some.injEq] at hmover
      subst i
      change Unit ≃ Unit
      exact Equiv.refl Unit
  | terminal =>
      rw [hstate] at hmover
      exact (Option.some_ne_none i hmover.symm).elim

/-- The observed game with uncountably many unused player identifiers. -/
def observed : ObservedGame Player Unit where
  base := base
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := fun _ _ => rfl
  InfoState := sparseInfoState
  infoObserve := fun _ _ => ()
  infoAt := sparseInformationAt
  infoAt_observe := fun _ _ _ _ => rfl
  InfoAction := sparseInfoAction
  actionEquiv := sparseActionEquiv

/-- The one-decision game has no chance nodes. -/
theorem noChance :
    observed.base.NoChance := by
  intro state hnonterminal
  cases state with
  | decision =>
      exact ⟨activePlayer, rfl⟩
  | terminal =>
      exact
        (hnonterminal
          (show IsEmpty (observed.base.Action Node.terminal) from
            ⟨Empty.elim⟩)).elim

/-- The sparse-player observed game through the chance-aware API. -/
def game : ObservedChanceGame Player Unit :=
  { observed := observed
    chanceKernel := by
      intro history hchance
      cases hstate : history.1 with
      | decision =>
          have hmover := hchance.1
          change nodeMover history.1 = none at hmover
          rw [hstate] at hmover
          exact (Option.some_ne_none activePlayer hmover).elim
      | terminal =>
          apply (hchance.2 ?_).elim
          rw [hstate]
          exact
            (show IsEmpty
                (observed.base.Action Node.terminal) from
              ⟨Empty.elim⟩) }

/-- The initial complete history. -/
def initialHistory :
    game.observed.base.toArena.HistoryFrom game.observed.base.init :=
  Arena.HistoryFrom.nil
    game.observed.base.toArena
    game.observed.base.init

/-- The unique terminal complete history. -/
def terminalHistory :
    game.observed.base.toArena.HistoryFrom game.observed.base.init :=
  ⟨Node.terminal, initialHistory.2.snoc ()⟩

/-- Every complete history is either the initial or terminal history. -/
theorem history_classify
    (history :
      game.observed.base.toArena.HistoryFrom
        game.observed.base.init) :
    history = initialHistory ∨ history = terminalHistory := by
  rcases history with ⟨state, path⟩
  refine Arena.History.rec
    (motive := fun state path =>
      (⟨state, path⟩ :
        game.observed.base.toArena.HistoryFrom
          game.observed.base.init) =
          initialHistory ∨
        (⟨state, path⟩ :
          game.observed.base.toArena.HistoryFrom
            game.observed.base.init) =
          terminalHistory)
    ?_ ?_ path
  · exact Or.inl rfl
  · intro state path action ih
    rcases ih with hinitial | hterminal
    · cases hinitial
      cases action
      exact Or.inr rfl
    · cases hterminal
      exact Empty.elim action

/-- A two-point cover of complete histories. -/
def historyCover :
    Fin 2 →
      game.observed.base.toArena.HistoryFrom
        game.observed.base.init
  | 0 => initialHistory
  | 1 => terminalHistory

theorem historyCover_surjective :
    Function.Surjective historyCover := by
  intro history
  rcases history_classify history with hinitial | hterminal
  · exact ⟨0, hinitial.symm⟩
  · exact ⟨1, hterminal.symm⟩

noncomputable instance historyCountable :
    Countable
      (game.observed.base.toArena.HistoryFrom
        game.observed.base.init) :=
  historyCover_surjective.countable

/-- A singleton cover of the total complete-history/local-action carrier. The
terminal history contributes no element. -/
def completeHistoryActionCover :
    Unit →
      ObservedChanceGame.CompleteHistoryAction game :=
  fun _ => ⟨initialHistory, ()⟩

theorem completeHistoryActionCover_surjective :
    Function.Surjective completeHistoryActionCover := by
  intro historyAction
  rcases historyAction with ⟨history, action⟩
  rcases history_classify history with hinitial | hterminal
  · subst history
    change Unit at action
    cases action
    exact ⟨(), rfl⟩
  · subst history
    change Empty at action
    exact Empty.elim action

noncomputable instance completeHistoryActionCountable :
    Countable
      (ObservedChanceGame.CompleteHistoryAction game) :=
  completeHistoryActionCover_surjective.countable

/-- The ambient player identifier type is genuinely not countable. -/
theorem player_not_countable :
    ¬ Countable Player := by
  intro hcountable
  letI : Countable Player := hcountable
  have hinjective :
      Function.Injective
        (fun value : ℝ => (Sum.inr value : Player)) :=
    Sum.inr_injective
  have hreal : Countable ℝ :=
    hinjective.countable
  exact (not_countable (α := ℝ)) hreal

/-- Each unused player has an uncountable declared information fiber. -/
theorem unused_information_not_countable
    (identifier : ℝ) :
    ¬ Countable
      (game.observed.InfoState
        (Sum.inr identifier : Player)) := by
  change ¬ Countable ℝ
  exact not_countable

/-- Each unreachable information point of an unused player has an uncountable
declared action fiber. -/
theorem unused_action_not_countable
    (identifier information : ℝ) :
    ¬ Countable
      (game.observed.InfoAction
        (Sum.inr identifier : Player)
        information) := by
  change ¬ Countable ℝ
  exact not_countable

/-- The total original player-information carrier is uncountable, confirming
that the constructor now counts only its reachable subtype. -/
theorem player_information_not_countable :
    ¬ Countable
      (ObservedChanceGame.PlayerInformationPoint game) := by
  intro hcountable
  letI :
      Countable
        (ObservedChanceGame.PlayerInformationPoint game) :=
    hcountable
  let injection :
      ℝ → ObservedChanceGame.PlayerInformationPoint game :=
    fun information =>
      ⟨(Sum.inr 0 : Player), information⟩
  have hinjective : Function.Injective injection := by
    intro information₁ information₂ heq
    exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  exact
    (not_countable (α := ℝ))
      hinjective.countable

/-- The total original dependent information-action carrier is likewise
uncountable, so neither of the former player-side countability hypotheses is
available. -/
theorem player_information_action_not_countable :
    ¬ Countable
      (ObservedChanceGame.PlayerInformationAction game) := by
  intro hcountable
  letI :
      Countable
        (ObservedChanceGame.PlayerInformationAction game) :=
    hcountable
  let injection :
      ℝ → ObservedChanceGame.PlayerInformationAction game :=
    fun action => by
      change
        Σ information : (Σ i : Player, sparseInfoState i),
          sparseInfoAction information.1 information.2
      exact
        ⟨⟨(Sum.inr 0 : Player), (0 : ℝ)⟩, action⟩
  have hinjective : Function.Injective injection := by
    intro action₁ action₂ heq
    exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  exact
    (not_countable (α := ℝ))
      hinjective.countable

/-- The unique behavioral profile at the sole inhabited information point. -/
noncomputable def profile :
    game.observed.BehavioralProfile := by
  intro i information
  change sparseInfoState i at information
  change PMF (sparseInfoAction i information)
  cases i with
  | inl value =>
      cases value
      cases information
      exact PMF.pure ()
  | inr value =>
      change PMF ℝ
      exact PMF.pure 0

/-- The automatic presentation exists without a `Countable Player` instance. -/
noncomputable def presentation :
    game.AnalyticPresentation :=
  ObservedChanceGame.CountablePresentation.presentation game

/-- The canonical tagged information carrier is countable even though the
ambient player type and the total original information carrier are not.
Together with `presentation`, this records the strictly reachable
hypothesis boundary without quantifying over the presentation structure's
independent carrier universes. -/
theorem tagged_information_countable :
    Countable (ObservedChanceGame.CountableInformation game) :=
  inferInstance

/-- Compilation is still exactly the original concrete history-action kernel
at every event prefix. -/
theorem compiled_kernel_exact
    (time : ℕ)
    (events : game.AnalyticHistoryArena.EventPrefix time) :
    (presentation.toPolicy profile).toEventHistoryActionPolicy.kernel
        time events =
      (ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
        game profile).toMeasurable.kernel
        (MeasurableKernelArena.latestEventState time events) :=
  presentation.compiled_kernel profile time events

end Examples.ObservedChanceCountableSparsePlayersBoundary
