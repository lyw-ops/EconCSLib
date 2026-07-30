/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Execution
import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Realization

/-!
# EconCSLib.Examples.ExtensiveGame.RootScopedKuhn

Finite guarding example **N-2** for the root-scoped boundary of constructive
mixed-to-behavioral realization.

The one-player game has two decisions. The information state at the second
decision remembers the first action, so the game has perfect recall. A fair
coin selects either the always-false or always-true complete pure plan; the
resulting mixed plan therefore correlates choices across information states.

The existing Kuhn construction behavioralizes this plan relative to an
explicitly selected continuation root. The named theorems below prove both
sides of the semantic boundary:

* exact bounded payoff-law realization and deviation coverage at every
  separately selected root; and
* a universally quantified impossibility theorem: no single behavioral
  profile realizes both the initial-root law at fuel `2` and the freshly
  resampled post-`false` continuation law at fuel `1`.

The negative theorem rules out the incorrect root-independent global lift. It
does not challenge either root-scoped construction, finite Kuhn rootwise-Nash
transfer, or the usual realization equivalence at one selected root. Mixed and
behavioral strategies also remain different strategy objects even where their
induced laws agree.
-/

namespace Examples.RootScopedKuhn

open ExtensiveGame

/-- Finite stages of the two-decision perfect-recall game. -/
inductive Stage
  | start
  | after (first : Bool)
  | done (first second : Bool)
  deriving DecidableEq, Fintype

/-- Both decision stages offer a Boolean action; completed stages are
terminal. -/
def stageAction : Stage → Type
  | .start => Bool
  | .after _ => Bool
  | .done _ _ => PEmpty

/-- The first action is retained in the intermediate state and both actions
are retained at the terminal state. -/
def stageNext : (stage : Stage) → stageAction stage → Stage
  | .start, first => .after first
  | .after first, second => .done first second
  | .done _ _, action => nomatch action

/-- The sole player controls both decision stages. -/
def stageMover : Stage → Option Unit
  | .start => some ()
  | .after _ => some ()
  | .done _ _ => none

/-- Terminal payoffs record both actions, making complete bounded laws
observable. -/
def payoff : Stage → Unit → Bool × Bool
  | .done first second, _ => (first, second)
  | _, _ => (false, false)

/-- Base deterministic extensive game for the root-scoped Kuhn regression. -/
def base : ExtensiveGame Unit (Bool × Bool) where
  State := Stage
  Action := stageAction
  next := stageNext
  init := .start
  mover := stageMover
  payoff := payoff

/-- Perfect-recall decision information: the second information state records
the first action. -/
inductive DecisionInfo
  | first
  | second (firstAction : Bool)
  deriving DecidableEq, Fintype

/-- The observation associated with each game stage. -/
def observe : Stage → Option DecisionInfo
  | .start => some .first
  | .after first => some (.second first)
  | .done _ _ => none

/-- Extract decision information from a player-controlled stage. -/
def infoAtState :
    (stage : Stage) → stageMover stage = some () → DecisionInfo
  | .start, _ => .first
  | .after first, _ => .second first
  | .done _ _, h => absurd h (by simp [stageMover])

/-- Boolean abstract actions coincide with concrete legal actions at both
decision stages. -/
def actionEquiv :
    (stage : Stage) → stageMover stage = some () →
      (Bool ≃ stageAction stage)
  | .start, _ => Equiv.refl Bool
  | .after _, _ => Equiv.refl Bool
  | .done _ _, h => absurd h (by simp [stageMover])

private theorem infoAtState_observe (stage : Stage)
    (hmover : stageMover stage = some ()) :
    some (infoAtState stage hmover) = observe stage := by
  cases stage <;>
    simp [infoAtState, observe, stageMover] at hmover ⊢

/-- The finite observed game whose second decision remembers the first
action. -/
def observed : ObservedGame Unit (Bool × Bool) where
  base := base
  Observation := fun _ => Option DecisionInfo
  PublicObservation := Option DecisionInfo
  observe := fun _ history => observe history.1
  publicObserve := fun history => observe history.1
  publicOf := fun _ observation => observation
  observe_public := fun _ _ => rfl
  InfoState := fun _ => DecisionInfo
  infoObserve := fun _ information => some information
  infoAt := fun history _ hmover =>
    infoAtState history.1 hmover
  infoAt_observe := by
    intro history i hmover
    cases i
    exact infoAtState_observe history.1 hmover
  InfoAction := fun _ _ => Bool
  actionEquiv := fun history _ hmover =>
    actionEquiv history.1 hmover
  IsDesignatedContinuationRoot := fun _ => True
  init_isDesignatedContinuationRoot := trivial

private theorem ownDecisionHistory_at_mover
    (history :
      observed.base.toArena.HistoryFrom
        observed.base.init)
    (hmover :
      observed.base.mover history.1 = some ()) :
    observed.ownDecisionHistory () history =
      match history.1 with
      | .start => []
      | .after first =>
          [⟨DecisionInfo.first, first⟩]
      | .done _ _ => [] := by
  rcases history with ⟨finish, path⟩
  induction path with
  | nil => rfl
  | @snoc previous path action ih =>
      cases previous with
      | start =>
          have hpath := ih rfl
          change
            observed.ownDecisionHistoryPath () path =
              [] at hpath
          change
            observed.ownDecisionHistoryPath () path ++
                [⟨DecisionInfo.first, action⟩] =
              [⟨DecisionInfo.first, action⟩]
          rw [hpath]
          rfl
      | after first =>
          simp [observed, base, stageNext, stageMover] at hmover
      | done first second => exact nomatch action

/-- The concrete finite game has perfect recall: equal second-stage
information states remember the same first action. -/
theorem observed_perfectRecall :
    observed.PerfectRecall := by
  intro i
  cases i
  intro first second hfirst hsecond hsame
  rw [ownDecisionHistory_at_mover first hfirst,
    ownDecisionHistory_at_mover second hsecond]
  rcases first with ⟨firstState, firstPath⟩
  rcases second with ⟨secondState, secondPath⟩
  cases firstState with
  | start =>
      cases secondState with
      | start => rfl
      | after action =>
          simp [observed, infoAtState] at hsame
      | done _ _ =>
          simp [observed, base, stageMover] at hsecond
  | after firstAction =>
      cases secondState with
      | start =>
          simp [observed, infoAtState] at hsame
      | after secondAction =>
          simpa [observed, infoAtState] using
            congrArg
              (fun information =>
                match information with
                | DecisionInfo.first => false
                | DecisionInfo.second action => action)
              hsame
      | done _ _ =>
          simp [observed, base, stageMover] at hsecond
  | done _ _ =>
      simp [observed, base, stageMover] at hfirst

/-- The hypotheses required by the constructive finite Kuhn API hold for the
concrete game. -/
def hypotheses :
    observed.FiniteKuhnHypotheses where
  perfectRecall := observed_perfectRecall
  finiteInfoState := by
    intro i
    change Finite DecisionInfo
    infer_instance

/-- The concrete game contains no chance-controlled decision stage. -/
theorem base_noChance : observed.base.NoChance := by
  intro state hnonterminal
  cases state with
  | start => exact ⟨(), rfl⟩
  | after first => exact ⟨(), rfl⟩
  | done first second =>
      exact
        (hnonterminal
          ⟨fun action => nomatch action⟩).elim

/-- View the deterministic example through the normalized chance-EFG API. -/
def chanceGame :
    ObservedChanceGame Unit (Bool × Bool) :=
  ObservedChanceGame.ofNoChance
    observed base_noChance

instance :
    (state : chanceGame.observed.base.State) →
      Decidable
        (chanceGame.observed.base.isTerminal state)
  | .start => isFalse (by
      intro h
      exact h.false false)
  | .after _ => isFalse (by
      intro h
      exact h.false false)
  | .done _ _ =>
      isTrue ⟨fun action => nomatch action⟩

/-- The initial continuation root. -/
def initialRoot :
    observed.base.toArena.HistoryFrom
      observed.base.init :=
  ⟨Stage.start, Arena.History.nil⟩

/-- The typed concrete action choosing `false` at the initial decision. -/
def chooseFalse :
    observed.base.Action Stage.start :=
  false

/-- A concrete second-stage continuation after choosing `false` first. -/
def afterFalseRoot :
    observed.base.toArena.HistoryFrom
      observed.base.init :=
  ⟨Stage.after false,
    Arena.History.nil.snoc chooseFalse⟩

/-- Fair Boolean law used to select a complete correlated plan. -/
noncomputable def fairCoin : PMF Bool :=
  PMF.bernoulli (1 / 2) (by norm_num)

/-- A complete pure plan choosing the same Boolean action at every information
state. -/
def constantPlan (choice : Bool) :
    observed.PureStrategy () :=
  fun _ => choice

/-- A mixed strategy supported on the always-false and always-true plans.
Choices at distinct information states are therefore perfectly correlated. -/
noncomputable def correlatedStrategy :
    observed.MixedStrategy () :=
  fairCoin.map constantPlan

/-- The one-player mixed profile carrying the correlated complete-plan law. -/
noncomputable def correlatedProfile :
    observed.MixedProfile :=
  fun _ => correlatedStrategy

/-! ### Explicit bounded-law calculations -/

private def payoffOutcome (first second : Bool) :
    Option (Unit → Bool × Bool) :=
  some (fun _ => (first, second))

private abbrev afterRoot (first : Bool) :
    observed.base.toArena.HistoryFrom observed.base.init :=
  ⟨.after first,
    Arena.History.nil.snoc
      (show observed.base.Action .start from first)⟩

private theorem afterStage_not_terminal (first : Bool) :
    ¬ chanceGame.observed.base.isTerminal (.after first) := by
  intro h
  exact h.false false

private theorem afterRoot_not_terminal (first : Bool) :
    ¬ chanceGame.observed.base.isTerminal (afterRoot first).1 :=
  afterStage_not_terminal first

private theorem done_terminal (first second : Bool) :
    base.isTerminal (.done first second) :=
  ⟨fun action => nomatch action⟩

private abbrev terminalRoot (first second : Bool) :
    observed.base.toArena.HistoryFrom observed.base.init :=
  ⟨.done first second,
    (afterRoot first).2.snoc
      (show observed.base.Action (.after first) from second)⟩

private theorem stoppedPayoff_terminalRoot (first second : Bool) :
    chanceGame.stoppedPayoffAtHistory (terminalRoot first second) =
      payoffOutcome first second := by
  unfold ObservedChanceGame.stoppedPayoffAtHistory
  have hterminal :
      chanceGame.observed.base.isTerminal
        (terminalRoot first second).1 :=
    done_terminal first second
  rw [if_pos hterminal]
  rfl

private theorem actionLaw_afterRoot
    (behavioral : observed.BehavioralProfile)
    (first : Bool) :
    (behavioral ()).actionLawAt observed (afterRoot first) rfl =
      behavioral () (.second first) := by
  unfold ObservedGame.BehavioralStrategy.actionLawAt
  change
    (behavioral () (.second first)).map id =
      behavioral () (.second first)
  exact PMF.map_id _

private theorem chanceActionLaw_afterRoot
    (behavioral : observed.BehavioralProfile)
    (first : Bool) :
    (behavioral ()).actionLawAt
        chanceGame.observed (afterRoot first) rfl =
      behavioral () (.second first) :=
  actionLaw_afterRoot behavioral first

private theorem behavioralLaw_afterRoot
    (behavioral : observed.BehavioralProfile)
    (first : Bool) :
    chanceGame.behavioralStoppedPayoffLawFrom
        behavioral (afterRoot first) 1 =
      (behavioral () (.second first)).map
        (fun second => payoffOutcome first second) := by
  unfold ObservedChanceGame.behavioralStoppedPayoffLawFrom
  rw [Arena.stochasticHistoryPMFFrom]
  simp only [afterStage_not_terminal, ↓reduceDIte]
  rw [ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_mover
    _ _ _ (afterRoot_not_terminal first) () rfl]
  unfold ObservedGame.BehavioralProfile.actionLawAt
  rw [chanceActionLaw_afterRoot]
  rw [PMF.map_bind]
  change
    (behavioral () (.second first)).bind
        (fun second =>
          (PMF.pure (terminalRoot first second)).map
            chanceGame.stoppedPayoffAtHistory) =
      _
  have hinner :
      (fun second =>
        (PMF.pure (terminalRoot first second)).map
          chanceGame.stoppedPayoffAtHistory) =
        (PMF.pure ∘
          fun second => payoffOutcome first second) := by
    funext second
    calc
      (PMF.pure (terminalRoot first second)).map
          chanceGame.stoppedPayoffAtHistory =
        PMF.pure
          (chanceGame.stoppedPayoffAtHistory
            (terminalRoot first second)) :=
        PMF.pure_map _ _
      _ = PMF.pure (payoffOutcome first second) :=
        congrArg PMF.pure
          (stoppedPayoff_terminalRoot first second)
  change
    (behavioral () (.second first)).bind
        (fun second =>
          (PMF.pure (terminalRoot first second)).map
            chanceGame.stoppedPayoffAtHistory) =
      _
  calc
    _ =
        (behavioral () (.second first)).bind
          (PMF.pure ∘
            fun second => payoffOutcome first second) :=
      congrArg
        (fun continuation =>
          (behavioral () (.second first)).bind continuation)
        hinner
    _ = _ :=
      PMF.bind_pure_comp
        (fun second => payoffOutcome first second)
        (behavioral () (.second first))

private theorem afterFalseRoot_eq :
    afterFalseRoot = afterRoot false :=
  rfl

private theorem initial_not_terminal :
    ¬ chanceGame.observed.base.isTerminal initialRoot.1 := by
  intro h
  exact h.false false

private theorem actionLaw_initial
    (behavioral : observed.BehavioralProfile) :
    (behavioral ()).actionLawAt
        chanceGame.observed initialRoot rfl =
      behavioral () .first := by
  unfold ObservedGame.BehavioralStrategy.actionLawAt
  change
    (behavioral () .first).map id =
      behavioral () .first
  exact PMF.map_id _

private theorem behavioralLaw_initial
    (behavioral : observed.BehavioralProfile) :
    chanceGame.behavioralStoppedPayoffLawFrom
        behavioral initialRoot 2 =
      (behavioral () .first).bind fun first =>
        (behavioral () (.second first)).map
          (fun second => payoffOutcome first second) := by
  unfold ObservedChanceGame.behavioralStoppedPayoffLawFrom
  rw [Arena.stochasticHistoryPMFFrom]
  simp only [initial_not_terminal, ↓reduceDIte]
  rw [ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_mover
    _ _ _ initial_not_terminal () rfl]
  unfold ObservedGame.BehavioralProfile.actionLawAt
  rw [actionLaw_initial]
  rw [PMF.map_bind]
  have hinner :
      (fun first =>
        (chanceGame.observed.base.toArena.stochasticHistoryPMFFrom
          (ObservedChanceGame.BehavioralProfile.toHistoryPolicy
            chanceGame behavioral)
          (afterRoot first) 1).map
            chanceGame.stoppedPayoffAtHistory) =
        (fun first =>
          (behavioral () (.second first)).map
            (fun second => payoffOutcome first second)) := by
    funext first
    change
      chanceGame.behavioralStoppedPayoffLawFrom
          behavioral (afterRoot first) 1 =
        _
    exact behavioralLaw_afterRoot behavioral first
  change
    (behavioral () .first).bind
        (fun first =>
          (chanceGame.observed.base.toArena.stochasticHistoryPMFFrom
            (ObservedChanceGame.BehavioralProfile.toHistoryPolicy
              chanceGame behavioral)
            (afterRoot first) 1).map
              chanceGame.stoppedPayoffAtHistory) =
      _
  exact congrArg
    (fun continuation =>
      (behavioral () .first).bind continuation)
    hinner

private theorem payoffOutcome_injective (first : Bool) :
    Function.Injective (payoffOutcome first) := by
  intro left right h
  have hsecond :=
    congrArg
      (fun outcome =>
        Option.map (fun value => (value ()).2) outcome)
      h
  simpa [payoffOutcome] using hsecond

private theorem payoffOutcome_ne_of_first_ne
    {first other : Bool} (hne : first ≠ other)
    (second otherSecond : Bool) :
    payoffOutcome first second ≠
      payoffOutcome other otherSecond := by
  intro h
  have hfirst :=
    congrArg
      (fun outcome =>
        Option.map (fun value => (value ()).1) outcome)
      h
  exact hne (by simpa [payoffOutcome] using hfirst)

private theorem behavioralLaw_initial_apply_false
    (behavioral : observed.BehavioralProfile)
    (second : Bool) :
    chanceGame.behavioralStoppedPayoffLawFrom
        behavioral initialRoot 2
        (payoffOutcome false second) =
      behavioral () .first false *
        behavioral () (.second false) second := by
  rw [behavioralLaw_initial]
  rw [PMF.bind_apply]
  change
    (∑' first : Bool,
      behavioral () .first first *
        (behavioral () (.second first)).map
          (payoffOutcome first)
          (payoffOutcome false second)) =
      _
  rw [tsum_bool]
  have hfalse :
      (behavioral () (.second false)).map
          (payoffOutcome false)
          (payoffOutcome false second) =
        behavioral () (.second false) second :=
    PMF.map_apply_of_injective
      (behavioral () (.second false))
      (payoffOutcome false)
      (payoffOutcome_injective false)
      second
  simp only [hfalse]
  simp [PMF.map_apply, payoffOutcome_ne_of_first_ne]

private theorem behavioralLaw_afterFalse_apply
    (behavioral : observed.BehavioralProfile)
    (second : Bool) :
    chanceGame.behavioralStoppedPayoffLawFrom
        behavioral afterFalseRoot 1
        (payoffOutcome false second) =
      behavioral () (.second false) second := by
  rw [afterFalseRoot_eq, behavioralLaw_afterRoot]
  exact
    PMF.map_apply_of_injective
      (behavioral () (.second false))
      (payoffOutcome false)
      (payoffOutcome_injective false)
      second

private def singletonProfileEquiv :
    observed.PureStrategy () ≃ observed.PureProfile where
  toFun := fun strategy _ => strategy
  invFun := fun profile => profile ()
  left_inv := fun _ => rfl
  right_inv := by
    intro profile
    funext i
    cases i
    rfl

private theorem correlatedProfile_pureProfileLaw :
    correlatedProfile.pureProfileLaw observed =
      correlatedStrategy.map singletonProfileEquiv := by
  ext profile
  unfold ObservedGame.MixedProfile.pureProfileLaw
  calc
    PMF.fintypePi correlatedProfile profile =
        ∏ i : Unit, correlatedProfile i (profile i) :=
      PMF.fintypePi_apply correlatedProfile profile
    _ = correlatedStrategy (profile ()) := by
      simp [correlatedProfile]
    _ =
        (correlatedStrategy.map singletonProfileEquiv) profile := by
      rw [PMF.map_equiv_apply]
      rfl

private theorem correlatedProfile_pureProfileLaw_chance :
    correlatedProfile.pureProfileLaw chanceGame.observed =
      correlatedStrategy.map singletonProfileEquiv :=
  correlatedProfile_pureProfileLaw

private theorem constantProfile_behavioralLaw_initial (choice : Bool) :
    chanceGame.behavioralStoppedPayoffLawFrom
        ((singletonProfileEquiv
          (constantPlan choice)).toBehavioral observed)
        initialRoot 2 =
      PMF.pure (payoffOutcome choice choice) := by
  rw [behavioralLaw_initial]
  simp [singletonProfileEquiv,
    ObservedGame.PureProfile.toBehavioral,
    ObservedGame.PureStrategy.toBehavioral,
    constantPlan, PMF.pure_bind]
  exact PMF.pure_map _ _

private theorem constantProfile_behavioralLaw_afterFalse (choice : Bool) :
    chanceGame.behavioralStoppedPayoffLawFrom
        ((singletonProfileEquiv
          (constantPlan choice)).toBehavioral observed)
        afterFalseRoot 1 =
      PMF.pure (payoffOutcome false choice) := by
  rw [afterFalseRoot_eq, behavioralLaw_afterRoot]
  simp [singletonProfileEquiv,
    ObservedGame.PureProfile.toBehavioral,
    ObservedGame.PureStrategy.toBehavioral,
    constantPlan]
  exact PMF.pure_map _ _

private theorem mixedLaw_initial :
    chanceGame.mixedStoppedPayoffLawFrom
        correlatedProfile initialRoot 2 =
      fairCoin.map (fun choice => payoffOutcome choice choice) := by
  unfold ObservedChanceGame.mixedStoppedPayoffLawFrom
  rw [correlatedProfile_pureProfileLaw_chance]
  let continuation :=
    fun pureProfile : observed.PureProfile =>
      chanceGame.behavioralStoppedPayoffLawFrom
        (pureProfile.toBehavioral chanceGame.observed)
        initialRoot 2
  calc
    (correlatedStrategy.map singletonProfileEquiv).bind continuation =
        correlatedStrategy.bind
          (continuation ∘ singletonProfileEquiv) :=
      PMF.bind_map correlatedStrategy singletonProfileEquiv continuation
    _ =
        (fairCoin.map constantPlan).bind
          (continuation ∘ singletonProfileEquiv) := rfl
    _ =
        fairCoin.bind
          ((continuation ∘ singletonProfileEquiv) ∘ constantPlan) :=
      PMF.bind_map fairCoin constantPlan
        (continuation ∘ singletonProfileEquiv)
    _ =
        fairCoin.bind
          (PMF.pure ∘
            fun choice => payoffOutcome choice choice) := by
      apply congrArg (PMF.bind fairCoin)
      funext choice
      exact constantProfile_behavioralLaw_initial choice
    _ = _ :=
      PMF.bind_pure_comp
        (fun choice => payoffOutcome choice choice)
        fairCoin

private theorem mixedLaw_afterFalse :
    chanceGame.mixedStoppedPayoffLawFrom
        correlatedProfile afterFalseRoot 1 =
      fairCoin.map (payoffOutcome false) := by
  unfold ObservedChanceGame.mixedStoppedPayoffLawFrom
  rw [correlatedProfile_pureProfileLaw_chance]
  let continuation :=
    fun pureProfile : observed.PureProfile =>
      chanceGame.behavioralStoppedPayoffLawFrom
        (pureProfile.toBehavioral chanceGame.observed)
        afterFalseRoot 1
  calc
    (correlatedStrategy.map singletonProfileEquiv).bind continuation =
        correlatedStrategy.bind
          (continuation ∘ singletonProfileEquiv) :=
      PMF.bind_map correlatedStrategy singletonProfileEquiv continuation
    _ =
        (fairCoin.map constantPlan).bind
          (continuation ∘ singletonProfileEquiv) := rfl
    _ =
        fairCoin.bind
          ((continuation ∘ singletonProfileEquiv) ∘ constantPlan) :=
      PMF.bind_map fairCoin constantPlan
        (continuation ∘ singletonProfileEquiv)
    _ =
        fairCoin.bind
          (PMF.pure ∘ payoffOutcome false) := by
      apply congrArg (PMF.bind fairCoin)
      funext choice
      exact constantProfile_behavioralLaw_afterFalse choice
    _ = _ :=
      PMF.bind_pure_comp (payoffOutcome false) fairCoin

private theorem diagonalPayoffOutcome_injective :
    Function.Injective
      (fun choice => payoffOutcome choice choice) := by
  intro left right h
  have hfirst :=
    congrArg
      (fun outcome =>
        Option.map (fun value => (value ()).1) outcome)
      h
  simpa [payoffOutcome] using hfirst

private theorem mixedLaw_initial_falseFalse :
    chanceGame.mixedStoppedPayoffLawFrom
        correlatedProfile initialRoot 2
        (payoffOutcome false false) =
      (2⁻¹ : ENNReal) := by
  rw [mixedLaw_initial]
  rw [PMF.map_apply_of_injective
    fairCoin
    (fun choice => payoffOutcome choice choice)
    diagonalPayoffOutcome_injective
    false]
  simp [fairCoin, PMF.bernoulli_apply]

private theorem mixedLaw_initial_falseTrue :
    chanceGame.mixedStoppedPayoffLawFrom
        correlatedProfile initialRoot 2
        (payoffOutcome false true) =
      0 := by
  rw [mixedLaw_initial, PMF.map_apply]
  rw [tsum_bool]
  have hfalse :
      payoffOutcome false true ≠
        payoffOutcome false false :=
    fun h =>
      Bool.noConfusion
        (payoffOutcome_injective false h)
  have htrue :
      payoffOutcome false true ≠
        payoffOutcome true true :=
    payoffOutcome_ne_of_first_ne Bool.false_ne_true _ _
  simp [hfalse, htrue]

private theorem mixedLaw_afterFalse_apply (second : Bool) :
    chanceGame.mixedStoppedPayoffLawFrom
        correlatedProfile afterFalseRoot 1
        (payoffOutcome false second) =
      (2⁻¹ : ENNReal) := by
  rw [mixedLaw_afterFalse]
  rw [PMF.map_apply_of_injective
    fairCoin
    (payoffOutcome false)
    (payoffOutcome_injective false)
    second]
  cases second <;>
    simp [fairCoin, PMF.bernoulli_apply]

/-! ### Root-independent separation -/

/-- A behavioral profile realizes the correlated mixed plan at one selected
continuation when their bounded optional-payoff laws are literally equal. -/
def RealizesAt
    (current :
      observed.base.toArena.HistoryFrom observed.base.init)
    (fuel : ℕ)
    (behavioral : observed.BehavioralProfile) : Prop :=
  chanceGame.behavioralStoppedPayoffLawFrom
      behavioral current fuel =
    chanceGame.mixedStoppedPayoffLawFrom
      correlatedProfile current fuel

/-- **N-2, universal separation.** No single root-independent behavioral
profile realizes both the initial-root law and the freshly resampled
post-`false` continuation law of the correlated mixed plan.

This theorem quantifies over every behavioral profile; it is not inferred from
two canonical root-scoped constructions being unequal. The continuation law
forces equal mass on its two second actions, which would make the initial
behavioral masses of `(false, false)` and `(false, true)` agree. The mixed plan
assigns those terminal outcomes masses `1/2` and `0`, respectively.

The result rules out only the erroneous continuation-wide promotion. The
positive theorem `correlatedPlan_realizedAtSelectedRoot` below still realizes
the plan exactly at each root selected separately. -/
theorem no_rootIndependent_behavioralProfile :
    ∀ behavioral : observed.BehavioralProfile,
      ¬ (RealizesAt initialRoot 2 behavioral ∧
        RealizesAt afterFalseRoot 1 behavioral) := by
  intro behavioral hrealizes
  rcases hrealizes with ⟨hinitial, hcontinuation⟩
  have hcontinuationFalse :=
    congrArg
      (fun law : PMF (Option (Unit → Bool × Bool)) =>
        law (payoffOutcome false false))
      hcontinuation
  have hcontinuationTrue :=
    congrArg
      (fun law : PMF (Option (Unit → Bool × Bool)) =>
        law (payoffOutcome false true))
      hcontinuation
  dsimp only at hcontinuationFalse hcontinuationTrue
  rw [behavioralLaw_afterFalse_apply,
    mixedLaw_afterFalse_apply] at hcontinuationFalse
  rw [behavioralLaw_afterFalse_apply,
    mixedLaw_afterFalse_apply] at hcontinuationTrue
  have hsecond :
      behavioral () (.second false) false =
        behavioral () (.second false) true :=
    hcontinuationFalse.trans hcontinuationTrue.symm
  have hinitialFalse :=
    congrArg
      (fun law : PMF (Option (Unit → Bool × Bool)) =>
        law (payoffOutcome false false))
      hinitial
  have hinitialTrue :=
    congrArg
      (fun law : PMF (Option (Unit → Bool × Bool)) =>
        law (payoffOutcome false true))
      hinitial
  dsimp only at hinitialFalse hinitialTrue
  rw [behavioralLaw_initial_apply_false,
    mixedLaw_initial_falseFalse] at hinitialFalse
  rw [behavioralLaw_initial_apply_false,
    mixedLaw_initial_falseTrue] at hinitialTrue
  have hhalfZero : (2⁻¹ : ENNReal) = 0 :=
    hinitialFalse.symm.trans <|
      (congrArg
        (fun probability =>
          behavioral () .first false * probability)
        hsecond).trans hinitialTrue
  exact (by norm_num : (2⁻¹ : ENNReal) ≠ 0) hhalfZero

/-- **N-2.** At every explicitly selected continuation root, the existing
root-scoped behavioralization of the correlated mixed plan has exactly the
same bounded payoff law from that root.

The repeated `current` in both the construction and the law is the guarded
semantic boundary: this theorem supplies no root-independent
behavioralization. -/
theorem correlatedPlan_realizedAtSelectedRoot
    (current :
      observed.base.toArena.HistoryFrom
        observed.base.init)
    (fuel : ℕ) :
    chanceGame.mixedStoppedPayoffLawFrom
        correlatedProfile current fuel =
      chanceGame.behavioralStoppedPayoffLawFrom
        (hypotheses.mixedToBehavioralProfileAt
          observed current correlatedProfile)
        current fuel := by
  exact
    chanceGame.mixedToBehavioral_stoppedPayoffLawFrom
      hypotheses.recallCertificate
      correlatedProfile current fuel

/-- Root-scoped construction of the full finite-Kuhn realization certificate,
including exact deviation coverage, at a selected continuation. -/
noncomputable def realizationAt
    (current :
      observed.base.toArena.HistoryFrom
        observed.base.init)
    (fuel : ℕ) :
    chanceGame.MixedBehavioralRealizationAt
      current fuel :=
  chanceGame.finiteKuhnMixedBehavioralRealizationAt
    hypotheses current fuel

/-- **N-2 deviation guard.** Every unilateral behavioral deviation at the
selected root has an exactly matching mixed-plan deviation law at that same
root. This exercises the coverage field needed for two-way root Nash transfer
without constructing a continuation-wide behavioralization. -/
theorem correlatedPlan_deviationCoveredAtSelectedRoot
    (current :
      observed.base.toArena.HistoryFrom
        observed.base.init)
    (fuel : ℕ)
    (target : observed.BehavioralStrategy ()) :
    ∃ source : observed.MixedStrategy (),
      chanceGame.behavioralStoppedPayoffLawFrom
          (Function.update
            ((realizationAt current fuel).mapProfile
              correlatedProfile)
            () target)
          current fuel =
        chanceGame.mixedStoppedPayoffLawFrom
          (Function.update
            correlatedProfile () source)
          current fuel := by
  simpa
      [ObservedChanceGame.MixedBehavioralRealizationAt.mapProfile] using
    (realizationAt current fuel).realize_deviation
      correlatedProfile () target

end Examples.RootScopedKuhn
