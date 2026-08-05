/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.NormNum

/-!
# Stochastic-tree compilation regression

This example checks the public discrete-compilation facade, the exact
constructor chance law at the root, and the bounded endpoint/payoff-law
preservation theorems for `StochasticGameTree`.
-/

namespace Examples.ExtensiveGame.StochasticTreeCompilation

open StochasticGameTree

/-- The normalized uniform law on the two fair-coin child occurrences. -/
noncomputable def fairCoinLaw : PMF (Fin 2) :=
  PMF.ofFintype
    (fun _ => (2 : ENNReal)⁻¹)
    (by
      rw [Fin.sum_univ_two]
      exact ENNReal.inv_two_add_inv_two)

/-- Each occurrence has probability one half under `fairCoinLaw`. -/
theorem fairCoinLaw_apply (choice : Fin 2) :
    (fairCoinLaw choice).toReal = 1 / 2 := by
  norm_num [fairCoinLaw, PMF.ofFintype_apply]

/-- The real-valued finite weights of `fairCoinLaw` sum to one. -/
theorem fairCoinLaw_total :
    ∑ choice : Fin 2, (fairCoinLaw choice).toReal = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [fairCoinLaw_apply]

/-- A one-step fair coin game for examples and CI regression checks. -/
noncomputable def fairCoinGame : StochasticGameTree (Fin 2) :=
  StochasticGameTree.Chance 1
    (fun choice =>
      if choice = 0 then
        StochasticGameTree.Leaf (fun i => if i = 0 then 1 else 0)
      else
        StochasticGameTree.Leaf (fun i => if i = 0 then 0 else 1))
    fairCoinLaw

/-- At fuel two, the fair-coin regression game gives player zero expected
payoff one half. -/
theorem fairCoin_expected_player0 :
    expectedPayoffAtFuel 2 (headPolicy : Policy (Fin 2))
      fairCoinGame 0 = 1 / 2 := by
  simp only [expectedPayoffAtFuel, expectedPayoffWithFuel, fairCoinGame,
    fairCoinLaw_apply, Nat.reduceAdd]
  rw [Fin.sum_univ_two]
  simp

/-- Empty complete history of the fair-coin source tree. -/
noncomputable def initialHistory :
    (toExtensiveGame fairCoinGame).toArena.HistoryFrom fairCoinGame :=
  Arena.HistoryFrom.nil
    (toExtensiveGame fairCoinGame).toArena fairCoinGame

/-- The fair-coin root is a genuine nonterminal chance state. -/
theorem initialHistory_isChance :
    (toExtensiveGame fairCoinGame).isChanceState
      initialHistory.1 := by
  constructor
  · rfl
  · exact
      toExtensiveGame_not_isTerminal_chance
        fairCoinGame 1
        (fun choice =>
          if choice = 0 then
            .Leaf (fun i => if i = 0 then 1 else 0)
          else
            .Leaf (fun i => if i = 0 then 0 else 1))
        fairCoinLaw

/-- The compiler does not reconstruct or renormalize the source coin law. -/
theorem compiledChanceKernel_eq_fairCoinLaw :
    (toObservedChanceGame fairCoinGame).chanceKernel
        initialHistory initialHistory_isChance =
      fairCoinLaw := by
  rfl

/-- One bounded compiled step has exactly the recursively defined source
endpoint law after complete histories are forgotten. -/
theorem compiledEndpointLaw_one :
    ((toExtensiveGame fairCoinGame).toArena.stochasticHistoryPMFFrom
        (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
          (toObservedChanceGame fairCoinGame)
          (policyToBehavioralProfile fairCoinGame headPolicy))
        initialHistory 1).map Sigma.fst =
      endpointLawWithFuel 1 headPolicy [] fairCoinGame := by
  simpa [initialHistory] using
    stochasticHistoryPMFFrom_map_endpoint
      fairCoinGame headPolicy initialHistory 1

/-- The same execution also preserves the complete vector-valued payoff law. -/
theorem compiledPayoffLaw_one :
    ((toExtensiveGame fairCoinGame).toArena.stochasticHistoryPMFFrom
        (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
          (toObservedChanceGame fairCoinGame)
          (policyToBehavioralProfile fairCoinGame headPolicy))
        initialHistory 1).map
          (fun history =>
            (toExtensiveGame fairCoinGame).payoff history.1) =
      (endpointLawWithFuel 1 headPolicy [] fairCoinGame).map
        statePayoff := by
  simpa [initialHistory] using
    stochasticHistoryPMFFrom_map_payoff
      fairCoinGame headPolicy initialHistory 1

end Examples.ExtensiveGame.StochasticTreeCompilation
