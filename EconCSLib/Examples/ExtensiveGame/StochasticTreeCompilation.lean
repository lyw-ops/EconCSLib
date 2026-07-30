/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete

/-!
# Stochastic-tree compilation regression

This example checks the public discrete-compilation facade, the exact
constructor chance law at the root, and the bounded endpoint/payoff-law
preservation theorems for `StochasticGameTree`.
-/

namespace Examples.ExtensiveGame.StochasticTreeCompilation

open StochasticGameTree

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
