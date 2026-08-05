/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.SequentialEquilibrium

/-!
# Off-path beliefs change local sequential rationality

Player `0` can stay out at the root or enter. After entry, chance selects one
of two hidden types and player `1` moves without observing the type. The two
type histories are distinct complete-history occurrences in one information
state.

The displayed behavioral profile stays out with probability one, so player
`1`'s information state is off path. We then use the experimental
sequential-decision-evaluator interface to encode the continuation decision:
action `false` is optimal under the low-type belief and action `true` is
optimal under the high-type belief. The same behavioral profile is locally
sequentially rational under the first assessment and not under the second.

This example does not claim either assessment is Kreps--Wilson consistent;
its purpose is the narrower regression that beliefs are occurrence-sensitive
and can matter at information states missed by on-path best-response checks.
-/

namespace Examples.OffPathBeliefRationality

open ExtensiveGame
open scoped ENNReal

/-- Root, outside option, chance node, two hidden-type nodes, and terminal
responses. -/
inductive State
  | root
  | outside
  | chance
  | hidden (high : Bool)
  | terminal (high response : Bool)
  deriving DecidableEq

/-- Entry and response choices are Boolean; chance also selects a Boolean
type. Terminal and outside-option states have no actions. -/
def Action : State → Type
  | .root => Bool
  | .outside => Empty
  | .chance => Bool
  | .hidden _ => Bool
  | .terminal _ _ => Empty

/-- `false` stays out, `true` enters; chance then selects a hidden type. -/
def next : (state : State) → Action state → State
  | .root, false => .outside
  | .root, true => .chance
  | .chance, high => .hidden high
  | .hidden high, response => .terminal high response

/-- Player `0` owns the entry decision and player `1` owns the hidden-type
response decision. -/
def mover : State → Option (Fin 2)
  | .root => some 0
  | .hidden _ => some 1
  | .outside | .chance | .terminal _ _ => none

/-- Compact state game; the evaluator below supplies the local continuation
values relevant to the regression. -/
def base : ExtensiveGame (Fin 2) ℝ where
  State := State
  Action := Action
  next := next
  init := .root
  mover := mover
  payoff := fun _ _ => 0

/-- Both players have one decision information state. In particular, player
`1` cannot observe the hidden type. -/
def observed : ObservedGame (Fin 2) ℝ where
  base := base
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := by simp
  InfoState := fun _ => Unit
  infoObserve := fun _ _ => ()
  infoAt := fun _ _ _ _ => ()
  infoAt_observe := by simp
  InfoAction := fun _ _ => Bool
  actionEquiv := by
    intro history i hmover _hnonterminal
    cases hstate : history.1 with
    | root =>
        change Bool ≃ Bool
        exact Equiv.refl Bool
    | outside =>
        change mover history.1 = some i at hmover
        rw [hstate] at hmover
        contradiction
    | chance =>
        change mover history.1 = some i at hmover
        rw [hstate] at hmover
        contradiction
    | hidden high =>
        change Bool ≃ Bool
        exact Equiv.refl Bool
    | terminal high response =>
        change mover history.1 = some i at hmover
        rw [hstate] at hmover
        contradiction

/-- Explicit chance law. A point mass is sufficient here because the
off-path distinction is about possible complete history occurrences rather
than a consistency claim. -/
noncomputable def game : ObservedChanceGame (Fin 2) ℝ where
  observed := observed
  chanceKernel := by
    intro history hchance
    cases hstate : history.1 with
    | root =>
        have hmover := hchance.1
        change mover history.1 = none at hmover
        rw [hstate] at hmover
        contradiction
    | outside =>
        exact
          (hchance.2 (by
            rw [hstate]
            change IsEmpty Empty
            exact ⟨Empty.elim⟩)).elim
    | chance =>
        simpa [base, Action, hstate] using
          (PMF.pure false : PMF Bool)
    | hidden high =>
        have hmover := hchance.1
        change mover history.1 = none at hmover
        rw [hstate] at hmover
        contradiction
    | terminal high response =>
        exact
          (hchance.2 (by
            rw [hstate]
            change IsEmpty Empty
            exact ⟨Empty.elim⟩)).elim

/-- Empty root history. -/
def initial : base.toArena.HistoryFrom base.init :=
  Arena.HistoryFrom.nil base.toArena base.init

/-- History after player `0` enters. -/
def afterEntry : base.toArena.HistoryFrom base.init :=
  ⟨.chance, initial.2.snoc true⟩

/-- Hidden-type decision history after entry and the chance selection. -/
def afterType (high : Bool) :
    base.toArena.HistoryFrom base.init :=
  ⟨.hidden high, afterEntry.2.snoc high⟩

/-- Root occurrence witnessing player `0`'s information state. -/
def rootOccurrence :
    game.observed.DecisionInfoWitness 0 () where
  history := initial
  mover := rfl
  nonterminal := fun hterminal => hterminal.false false
  infoAt_eq := rfl

/-- Low-type occurrence in player `1`'s information state. -/
def lowOccurrence :
    game.observed.DecisionInfoWitness 1 () where
  history := afterType false
  mover := rfl
  nonterminal := fun hterminal => hterminal.false false
  infoAt_eq := rfl

/-- High-type occurrence in the same player-`1` information state. -/
def highOccurrence :
    game.observed.DecisionInfoWitness 1 () where
  history := afterType true
  mover := rfl
  nonterminal := fun hterminal => hterminal.false false
  infoAt_eq := rfl

/-- The two belief points are distinct complete-history occurrences. -/
theorem lowOccurrence_ne_highOccurrence :
    lowOccurrence ≠ highOccurrence := by
  intro heq
  have hhistory :=
    congrArg
      (fun occurrence =>
        occurrence.history.1)
      heq
  have hbool : false = true :=
    State.hidden.inj hhistory
  exact Bool.false_ne_true hbool

/-- Both hidden histories are classified into the same information state. -/
theorem hidden_histories_same_information :
    game.observed.infoAt
        (afterType false) 1 rfl
        (fun hterminal => hterminal.false false) =
      game.observed.infoAt
        (afterType true) 1 rfl
        (fun hterminal => hterminal.false false) :=
  rfl

/-- The behavioral profile stays out and prescribes response `false`. -/
noncomputable def behavior :
    game.observed.BehavioralProfile :=
  fun _ _ => PMF.pure false

/-- Entry has zero probability under the displayed behavior, hence the
hidden-type information state is missed by on-path checks. -/
@[simp]
theorem behavior_entry_probability :
    behavior 0 () true = 0 := by
  simp [behavior]

/-- The two deterministic response laws are different. -/
theorem pure_false_ne_pure_true :
    (PMF.pure false : PMF Bool) ≠ PMF.pure true := by
  intro heq
  have hpoint :=
    congrArg (fun law : PMF Bool => law false) heq
  simp at hpoint

/-- Belief system concentrated on the low-type occurrence for player `1`. -/
noncomputable def lowBeliefs : game.BeliefSystem := by
  classical
  intro i information
  by_cases hi : i = 1
  · subst i
    cases information
    exact PMF.pure lowOccurrence
  · have hi0 : i = 0 := by
      fin_cases i
      · rfl
      · exact (hi rfl).elim
    subst i
    cases information
    exact PMF.pure rootOccurrence

/-- Belief system concentrated on the high-type occurrence for player `1`. -/
noncomputable def highBeliefs : game.BeliefSystem := by
  classical
  intro i information
  by_cases hi : i = 1
  · subst i
    cases information
    exact PMF.pure highOccurrence
  · have hi0 : i = 0 := by
      fin_cases i
      · rfl
      · exact (hi rfl).elim
    subst i
    cases information
    exact PMF.pure rootOccurrence

/-- Same behavior paired with the low-type off-path belief. -/
noncomputable def lowAssessment : game.Assessment where
  behavior := behavior
  beliefs := lowBeliefs

/-- Same behavior paired with the high-type off-path belief. -/
noncomputable def highAssessment : game.Assessment where
  behavior := behavior
  beliefs := highBeliefs

/-- The low assessment gives the low occurrence probability one. -/
@[simp]
theorem lowAssessment_lowOccurrence :
    lowAssessment.beliefs 1 () lowOccurrence = 1 := by
  simp [lowAssessment, lowBeliefs]

/-- The high assessment gives the low occurrence probability zero. -/
@[simp]
theorem highAssessment_lowOccurrence :
    highAssessment.beliefs 1 () lowOccurrence = 0 := by
  simp [highAssessment, highBeliefs,
    lowOccurrence_ne_highOccurrence]

/-- Local hidden-type decision evaluator.

For player `1`, response `false` is uniquely best when the belief is
concentrated on the low occurrence; otherwise response `true` is uniquely
best. Player `0`'s value is constant because only the off-path response
regression matters here. -/
noncomputable def evaluator :
    game.SequentialDecisionEvaluator where
  value := by
    classical
    intro assessment i information deviation
    by_cases hi : i = 1
    · subst i
      cases information
      exact
        if assessment.beliefs 1 () lowOccurrence = 1 then
          if deviation = PMF.pure false then 1 else 0
        else
          if deviation = PMF.pure true then 1 else 0
    · exact 0

/-- Under the low belief, deterministic response `false` receives value one.
-/
theorem evaluator_lowAssessment_prescribed :
    evaluator.value lowAssessment 1 ()
        (PMF.pure false) =
      1 := by
  classical
  simp [evaluator]
  exact rfl

/-- Under the low belief, every other response law receives value zero. -/
theorem evaluator_lowAssessment_other
    (deviation : PMF Bool)
    (hne : deviation ≠ PMF.pure false) :
    evaluator.value lowAssessment 1 () deviation = 0 := by
  classical
  simp [evaluator]
  exact hne

/-- Under the high belief, deterministic response `true` receives value one.
-/
theorem evaluator_highAssessment_deviation :
    evaluator.value highAssessment 1 ()
        (PMF.pure true) =
      1 := by
  classical
  simp [evaluator]
  exact rfl

/-- Under the high belief, deterministic response `false` receives value
zero. -/
theorem evaluator_highAssessment_prescribed :
    evaluator.value highAssessment 1 ()
        (PMF.pure false) =
      0 := by
  classical
  simp [evaluator]
  exact pure_false_ne_pure_true

/-- Under the low-type belief, the prescribed response `false` is locally
sequentially rational at the off-path information state. -/
theorem lowAssessment_sequentiallyRational :
    ObservedChanceGame.Assessment.IsSequentiallyRationalFor
      game lowAssessment evaluator := by
  intro i information deviation
  by_cases hi : i = 1
  · subst i
    cases information
    change
      evaluator.value lowAssessment 1 () deviation ≤
        evaluator.value lowAssessment 1 ()
          (PMF.pure false)
    rw [evaluator_lowAssessment_prescribed]
    by_cases hdeviation :
        deviation = (PMF.pure false : PMF Bool)
    · subst deviation
      exact le_of_eq evaluator_lowAssessment_prescribed
    · rw [evaluator_lowAssessment_other deviation hdeviation]
      norm_num
  · simp [evaluator, hi]

/-- Under the high-type belief, deviating to response `true` is strictly
better than the prescribed response `false`. -/
theorem highAssessment_not_sequentiallyRational :
    ¬ ObservedChanceGame.Assessment.IsSequentiallyRationalFor
      game highAssessment evaluator := by
  intro rational
  have h :=
    rational 1 ()
      (PMF.pure true : PMF Bool)
  change
    evaluator.value highAssessment 1 ()
        (PMF.pure true) ≤
      evaluator.value highAssessment 1 ()
        (PMF.pure false)
    at h
  rw [evaluator_highAssessment_deviation,
    evaluator_highAssessment_prescribed] at h
  norm_num at h

/-- The two assessments differ only in their off-path belief system. -/
theorem lowAssessment_behavior_eq_highAssessment :
    lowAssessment.behavior = highAssessment.behavior :=
  rfl

end Examples.OffPathBeliefRationality
