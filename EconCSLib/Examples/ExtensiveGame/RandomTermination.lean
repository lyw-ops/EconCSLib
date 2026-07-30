/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory
import Mathlib.Tactic

/-!
# Random finite-time termination regression

A fair root coin terminates immediately with payoff two or delays termination
for one event and pays one. A second policy terminates immediately with
probability one. The example computes distinct finite laws and utilities,
shows that the unfinished mass changes from one to one half to zero, proves
almost-sure termination, and instantiates expected terminal-payoff convergence.

This is a discrete event-time example; it does not claim continuous time.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Examples.RandomTermination

inductive State
  | root
  | delayed
  | win
  | small
  deriving DecidableEq, Countable

def arena : Arena where
  State := State
  Action
    | .root => Bool
    | .delayed => Unit
    | .win => PEmpty
    | .small => PEmpty
  next
    | .root, stop => if stop = true then .win else .delayed
    | .delayed, _ => .small

instance (s : arena.State) : Decidable (arena.IsTerminal s) := by
  cases s
  · exact isFalse fun h => h.false true
  · exact isFalse fun h => h.false ()
  · exact isTrue ⟨PEmpty.elim⟩
  · exact isTrue ⟨PEmpty.elim⟩

abbrev History := arena.HistoryFrom State.root

inductive HistoryCode
  | root
  | delayed
  | win
  | small
  deriving Countable

def decodeHistory : HistoryCode → History
  | .root => ⟨_, Arena.History.nil⟩
  | .delayed =>
      ⟨_, Arena.History.nil.snoc
        (show arena.Action State.root from false)⟩
  | .win =>
      ⟨_, Arena.History.nil.snoc
        (show arena.Action State.root from true)⟩
  | .small =>
      ⟨_,
        (Arena.History.nil.snoc
          (show arena.Action State.root from false)).snoc
          (show arena.Action
            (arena.next State.root false) from ())⟩

theorem history_exists_code :
    ∀ {state : arena.State}
      (history : arena.History State.root state),
      ∃ code, decodeHistory code = ⟨state, history⟩ := by
  intro state history
  induction history with
  | nil =>
    exact ⟨HistoryCode.root, rfl⟩
  | @snoc previous history action ih =>
    obtain ⟨code, hcode⟩ := ih
    cases code with
    | root =>
      cases hcode
      cases action
      · exact ⟨HistoryCode.delayed, rfl⟩
      · exact ⟨HistoryCode.win, rfl⟩
    | delayed =>
      cases hcode
      cases action
      exact ⟨HistoryCode.small, rfl⟩
    | win =>
      cases hcode
      change PEmpty at action
      exact PEmpty.elim action
    | small =>
      cases hcode
      change PEmpty at action
      exact PEmpty.elim action

theorem decodeHistory_surjective :
    Function.Surjective decodeHistory := by
  rintro ⟨state, history⟩
  exact history_exists_code history

instance : Countable History :=
  decodeHistory_surjective.countable

instance : MeasurableSpace History := ⊤

instance : MeasurableSingletonClass History := by
  infer_instance

def initial : History :=
  decodeHistory .root

def delayed : History :=
  decodeHistory .delayed

def win : History :=
  decodeHistory .win

def small : History :=
  decodeHistory .small

theorem initial_not_terminal :
    ¬ arena.IsTerminal initial.1 := by
  change ¬ IsEmpty Bool
  exact fun h => h.false true

theorem delayed_not_terminal :
    ¬ arena.IsTerminal delayed.1 := by
  change ¬ IsEmpty Unit
  exact fun h => h.false ()

theorem win_terminal :
    arena.IsTerminal win.1 := by
  change IsEmpty PEmpty
  exact ⟨PEmpty.elim⟩

theorem small_terminal :
    arena.IsTerminal small.1 := by
  change IsEmpty PEmpty
  exact ⟨PEmpty.elim⟩

noncomputable def balancedPolicy :
    arena.StochasticHistoryPolicy State.root :=
  fun history hnonterminal => by
    cases hstate : history.1 with
    | root =>
        simpa [arena, hstate] using
          PMF.bernoulli (1 / 2 : ℝ≥0) (by norm_num)
    | delayed =>
        exact PMF.pure ()
    | win =>
        exfalso
        apply hnonterminal
        rw [hstate]
        exact ⟨PEmpty.elim⟩
    | small =>
        exfalso
        apply hnonterminal
        rw [hstate]
        exact ⟨PEmpty.elim⟩

noncomputable def immediatePolicy :
    arena.StochasticHistoryPolicy State.root :=
  fun history hnonterminal => by
    cases hstate : history.1 with
    | root =>
        exact PMF.pure true
    | delayed =>
        exact PMF.pure ()
    | win =>
        exfalso
        apply hnonterminal
        rw [hstate]
        exact ⟨PEmpty.elim⟩
    | small =>
        exfalso
        apply hnonterminal
        rw [hstate]
        exact ⟨PEmpty.elim⟩

@[simp]
theorem balancedPolicy_initial :
    balancedPolicy initial initial_not_terminal =
      PMF.bernoulli (1 / 2 : ℝ≥0) (by norm_num) := by
  rw [balancedPolicy]
  rfl

@[simp]
theorem immediatePolicy_initial :
    immediatePolicy initial initial_not_terminal =
      PMF.pure true := by
  rw [immediatePolicy]
  rfl

@[simp]
theorem balancedPolicy_delayed :
    balancedPolicy delayed delayed_not_terminal =
      PMF.pure () := by
  rw [balancedPolicy]
  rfl

def rootExtension (stop : Bool) : History :=
  if stop = true then win else delayed

def finalExtension (stop : Bool) : History :=
  if stop = true then win else small

theorem balanced_one_step_law :
    arena.stochasticHistoryPMFFrom balancedPolicy initial 1 =
      (PMF.bernoulli (1 / 2 : ℝ≥0) (by norm_num)).map
        rootExtension := by
  rw [arena.stochasticHistoryPMFFrom_succ_of_not_terminal
    balancedPolicy initial 0 initial_not_terminal]
  rw [balancedPolicy_initial]
  simp only [arena.stochasticHistoryPMFFrom_zero]
  calc
    _ =
        (PMF.bernoulli (1 / 2 : ℝ≥0) (by norm_num)).map
          (fun action =>
            (⟨arena.next initial.1 action,
              initial.2.snoc action⟩ : History)) :=
      PMF.bind_pure_comp _ _
    _ = _ := by
      rw [show
        (fun action =>
          (⟨arena.next initial.1 action,
            initial.2.snoc action⟩ : History)) =
            rootExtension by
          funext stop
          cases stop <;> rfl]
      rfl

theorem immediate_one_step_law :
    arena.stochasticHistoryPMFFrom immediatePolicy initial 1 =
      PMF.pure win := by
  rw [arena.stochasticHistoryPMFFrom_succ_of_not_terminal
    immediatePolicy initial 0 initial_not_terminal]
  rw [immediatePolicy_initial]
  simp only [arena.stochasticHistoryPMFFrom_zero]
  change
    (PMF.pure true).bind
        (PMF.pure ∘ fun action =>
          (⟨arena.next initial.1 action,
            initial.2.snoc action⟩ : History)) =
      PMF.pure win
  rw [PMF.pure_bind]
  rfl

theorem balanced_two_step_law :
    arena.stochasticHistoryPMFFrom balancedPolicy initial 2 =
      (PMF.bernoulli (1 / 2 : ℝ≥0) (by norm_num)).map
        finalExtension := by
  rw [arena.stochasticHistoryPMFFrom_succ_of_not_terminal
    balancedPolicy initial 1 initial_not_terminal]
  rw [balancedPolicy_initial]
  calc
    _ =
        (PMF.bernoulli (1 / 2 : ℝ≥0) (by norm_num)).bind
          (PMF.pure ∘ finalExtension) := by
      apply congrArg
      funext stop
      cases stop
      · change
          arena.stochasticHistoryPMFFrom balancedPolicy delayed 1 =
            PMF.pure (finalExtension false)
        rw [arena.stochasticHistoryPMFFrom_succ_of_not_terminal
          balancedPolicy delayed 0 delayed_not_terminal]
        rw [balancedPolicy_delayed]
        simp [small, delayed, decodeHistory, arena, finalExtension]
        rfl
      · change
          arena.stochasticHistoryPMFFrom balancedPolicy win 1 =
            PMF.pure (finalExtension true)
        rw [arena.stochasticHistoryPMFFrom_succ_of_terminal
          balancedPolicy win 0 win_terminal]
        rfl
    _ = _ := PMF.bind_pure_comp _ _

theorem balanced_one_step_win_probability :
    (arena.stochasticHistoryPMFFrom balancedPolicy initial 1) win =
      (1 / 2 : ℝ≥0∞) := by
  rw [arena.stochasticHistoryPMFFrom_succ_of_not_terminal
    balancedPolicy initial 0 initial_not_terminal]
  rw [balancedPolicy_initial]
  simp only [arena.stochasticHistoryPMFFrom_zero]
  change
    ((PMF.bernoulli (1 / 2 : ℝ≥0) (by norm_num)).bind
      (PMF.pure ∘ fun action =>
        (⟨arena.next initial.1 action,
          initial.2.snoc action⟩ : History))) win =
      (1 / 2 : ℝ≥0∞)
  rw [PMF.bind_pure_comp]
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp [initial, win, decodeHistory, arena]

theorem immediate_one_step_win_probability :
    (arena.stochasticHistoryPMFFrom immediatePolicy initial 1) win = 1 := by
  rw [arena.stochasticHistoryPMFFrom_succ_of_not_terminal
    immediatePolicy initial 0 initial_not_terminal]
  rw [immediatePolicy_initial]
  simp only [arena.stochasticHistoryPMFFrom_zero]
  change
    ((PMF.pure true).bind
      (PMF.pure ∘ fun action =>
        (⟨arena.next initial.1 action,
          initial.2.snoc action⟩ : History))) win = 1
  rw [PMF.pure_bind]
  exact PMF.pure_apply_self _

theorem one_step_laws_differ :
    arena.stochasticHistoryPMFFrom balancedPolicy initial 1 ≠
      arena.stochasticHistoryPMFFrom immediatePolicy initial 1 := by
  intro heq
  have happly :=
    congrArg (fun p : PMF History => p win) heq
  change
    (arena.stochasticHistoryPMFFrom balancedPolicy initial 1) win =
      (arena.stochasticHistoryPMFFrom immediatePolicy initial 1) win at happly
  rw [balanced_one_step_win_probability,
    immediate_one_step_win_probability] at happly
  norm_num at happly

/-- Nonterminal complete histories in the random-termination arena. -/
def nonterminalHistories : Set History :=
  {history | ¬ arena.IsTerminal history.1}

theorem nonterminalHistories_measurable :
    MeasurableSet nonterminalHistories :=
  Set.to_countable _ |>.measurableSet

theorem rootExtension_preimage_nonterminal :
    rootExtension ⁻¹' nonterminalHistories = {false} := by
  ext stop
  cases stop <;>
    simp [rootExtension, nonterminalHistories, win_terminal,
      delayed_not_terminal]

theorem finalExtension_preimage_nonterminal :
    finalExtension ⁻¹' nonterminalHistories = ∅ := by
  ext stop
  cases stop <;>
    simp [finalExtension, nonterminalHistories, win_terminal,
      small_terminal]

/-- The infinite path law has exactly the bounded one-step marginal. -/
theorem balanced_path_marginal_one :
    (Arena.pathLaw balancedPolicy initial).map (fun path => path 1) =
      (arena.stochasticHistoryPMFFrom
        balancedPolicy initial 1).toMeasure :=
  Arena.pathLaw_finiteMarginal_eq_stochasticHistoryPMFFrom_toMeasure
    balancedPolicy initial 1

theorem balanced_noneMass_zero :
    Arena.noneMass balancedPolicy initial 0 = 1 := by
  change
    Arena.pathLaw balancedPolicy initial
      ((fun path => path 0) ⁻¹' nonterminalHistories) = 1
  rw [← Measure.map_apply (measurable_pi_apply 0)
    nonterminalHistories_measurable]
  rw [
    Arena.pathLaw_finiteMarginal_eq_stochasticHistoryPMFFrom_toMeasure
      balancedPolicy initial 0]
  rw [arena.stochasticHistoryPMFFrom_zero]
  rw [PMF.toMeasure_pure]
  rw [Measure.dirac_apply' _ nonterminalHistories_measurable]
  simp [nonterminalHistories, initial_not_terminal]

theorem balanced_noneMass_one :
    Arena.noneMass balancedPolicy initial 1 = (1 / 2 : ℝ≥0∞) := by
  change
    Arena.pathLaw balancedPolicy initial
      ((fun path => path 1) ⁻¹' nonterminalHistories) =
        (1 / 2 : ℝ≥0∞)
  rw [← Measure.map_apply (measurable_pi_apply 1)
    nonterminalHistories_measurable]
  rw [balanced_path_marginal_one]
  rw [balanced_one_step_law]
  rw [PMF.toMeasure_map_apply _ _ _
    (measurable_of_countable _)
    nonterminalHistories_measurable]
  rw [rootExtension_preimage_nonterminal]
  rw [PMF.toMeasure_apply_singleton]
  simp
  exact Set.to_countable _ |>.measurableSet

theorem balanced_noneMass_two :
    Arena.noneMass balancedPolicy initial 2 = 0 := by
  change
    Arena.pathLaw balancedPolicy initial
      ((fun path => path 2) ⁻¹' nonterminalHistories) = 0
  rw [← Measure.map_apply (measurable_pi_apply 2)
    nonterminalHistories_measurable]
  rw [
    Arena.pathLaw_finiteMarginal_eq_stochasticHistoryPMFFrom_toMeasure
      balancedPolicy initial 2]
  rw [balanced_two_step_law]
  rw [PMF.toMeasure_map_apply _ _ _
    (measurable_of_countable _)
    nonterminalHistories_measurable]
  rw [finalExtension_preimage_nonterminal]
  simp

theorem balanced_noneMass_strictly_changes :
    Arena.noneMass balancedPolicy initial 1 <
      Arena.noneMass balancedPolicy initial 0 ∧
    Arena.noneMass balancedPolicy initial 2 <
      Arena.noneMass balancedPolicy initial 1 := by
  rw [balanced_noneMass_zero, balanced_noneMass_one,
    balanced_noneMass_two]
  norm_num

theorem balanced_aeTerminates :
    Arena.AETerminates balancedPolicy initial := by
  have hterminalAtTwo :
      ∀ᵐ path ∂Arena.pathLaw balancedPolicy initial,
        arena.IsTerminal (path 2).1 := by
    have hcomplement :
        (Arena.unfinishedAt (A := arena)
          (start := State.root) 2)ᶜ ∈
            ae (Arena.pathLaw balancedPolicy initial) :=
      compl_mem_ae_iff.mpr balanced_noneMass_two
    filter_upwards [hcomplement] with path hpath
    simpa [Arena.unfinishedAt] using hpath
  filter_upwards [hterminalAtTwo] with path hterminal
  intro htop
  have hle :=
    MeasureTheory.hittingAfter_le_of_mem
      (u := Arena.historyCoordinateProcess
        (A := arena) (start := State.root))
      (s := Arena.terminalHistorySet
        (A := arena) (start := State.root))
      (n := 0) (i := 2) (ω := path)
      (by omega) hterminal
  change
    Arena.terminalTime (A := arena) (start := State.root) path ≤
      (2 : WithTop ℕ) at hle
  rw [htop] at hle
  simp at hle

theorem balanced_noneMass_tendsto_zero :
    Filter.Tendsto
      (Arena.noneMass balancedPolicy initial)
      Filter.atTop (nhds 0) :=
  Arena.noneMass_tendsto_zero_of_aeTerminates
    balancedPolicy initial balanced_aeTerminates

def payoff (history : History) : ℝ :=
  match history.1 with
  | .win => 2
  | .small => 1
  | .root => 0
  | .delayed => 0

theorem payoff_measurable : Measurable payoff :=
  measurable_of_countable _

/-- A nonconstant bounded-horizon utility: probability of reaching the
high-payoff terminal history by the selected fuel. -/
noncomputable def boundedWinUtility
    (policy : arena.StochasticHistoryPolicy State.root)
    (fuel : ℕ) : ℝ≥0∞ :=
  (arena.stochasticHistoryPMFFrom policy initial fuel) win

theorem balanced_utility_zero :
    boundedWinUtility balancedPolicy 0 = 0 := by
  rw [boundedWinUtility, arena.stochasticHistoryPMFFrom_zero]
  apply PMF.pure_apply_of_ne
  intro heq
  have hstate := congrArg Sigma.fst heq
  change State.win = State.root at hstate
  contradiction

theorem balanced_utility_one :
    boundedWinUtility balancedPolicy 1 = (1 / 2 : ℝ≥0∞) :=
  balanced_one_step_win_probability

theorem immediate_utility_one :
    boundedWinUtility immediatePolicy 1 = 1 :=
  immediate_one_step_win_probability

theorem horizon_changes_balanced_utility :
    boundedWinUtility balancedPolicy 0 ≠
      boundedWinUtility balancedPolicy 1 := by
  rw [balanced_utility_zero, balanced_utility_one]
  exact ne_of_lt (ENNReal.div_pos (by simp) (by simp))

theorem policies_have_different_utility :
    boundedWinUtility balancedPolicy 1 ≠
      boundedWinUtility immediatePolicy 1 := by
  rw [balanced_utility_one, immediate_utility_one]
  norm_num

theorem balanced_expectedPayoff_tendsto :
    Filter.Tendsto
      (fun n =>
        ∫ path, Arena.stoppedPayoff payoff n path
          ∂Arena.pathLaw balancedPolicy initial)
      Filter.atTop
      (nhds
        (∫ path, Arena.terminalPayoff payoff path
          ∂Arena.pathLaw balancedPolicy initial)) := by
  apply
    Arena.expectedStoppedPayoff_tendsto_of_dominated
      balancedPolicy initial payoff payoff_measurable
      (fun _ => 2)
  · intro n
    filter_upwards with path
    by_cases hterminal : arena.IsTerminal (path n).1
    · rw [Arena.stoppedPayoff, if_pos hterminal]
      cases hstate : (path n).1
      · have hterminal' := hterminal
        rw [hstate] at hterminal'
        exact False.elim (hterminal'.false true)
      · have hterminal' := hterminal
        rw [hstate] at hterminal'
        exact False.elim (hterminal'.false ())
      · simp [payoff, hstate]
      · simp [payoff, hstate]
    · rw [Arena.stoppedPayoff, if_neg hterminal]
      norm_num
  · exact MeasureTheory.integrable_const 2
  · exact balanced_aeTerminates

end Examples.RandomTermination
