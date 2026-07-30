/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTree
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/-!
# EconCSLib.GameTheory.ExtensiveGame.StochasticGameTree

Finite perfect-information game trees with normalized chance nodes.

This module intentionally keeps stochastic trees separate from the existing
no-chance `GameTree` type. A chance node contains a genuine `PMF` on the finite
nonempty type of child occurrences. Nonnegativity and total mass one are
therefore construction invariants rather than optional side conditions.

Operational player choices are indexed by the path of child indices from the
root. Equal subtree values at different occurrences can consequently receive
different choices.

## Main definitions

* `StochasticGameTree` — terminal, player, and chance nodes.
* `StochasticGameTree.Policy` — occurrence-sensitive pure contingent choices.
* `StochasticGameTree.expectedPayoffWithFuel` — executable fuel-bounded
  expected-payoff evaluator.
* `StochasticGameTree.expectedPayoffAtFuel` — root evaluator at an explicit
  finite horizon.
* `StochasticGameTree.ofGameTree` — embed ordinary no-chance trees.

The occurrence-sensitive compiler and its exact bounded-law theorems live in
`Compiler/StochasticGameTreeObserved.lean`.
-/

inductive StochasticGameTree (N : Type*) : Type _
  | Leaf (payoff : N → ℝ) : StochasticGameTree N
  | Player (mover : N) (arity : ℕ)
      (child : Fin (arity + 1) → StochasticGameTree N) :
      StochasticGameTree N
  | Chance (arity : ℕ)
      (child : Fin (arity + 1) → StochasticGameTree N)
      (law : PMF (Fin (arity + 1))) :
      StochasticGameTree N

namespace StochasticGameTree

variable {N : Type*}

/-- Turn a nonempty head-and-tail family into a function on its finite child
occurrence type. -/
def childrenOfList (head : StochasticGameTree N)
    (tail : List (StochasticGameTree N)) :
    Fin (tail.length + 1) → StochasticGameTree N
  | ⟨0, _⟩ => head
  | ⟨index + 1, hindex⟩ =>
      tail.get ⟨index, by omega⟩

/-- An occurrence-sensitive pure policy.

The first argument is the path of child indices from the root to the current
player node. It prevents equal subtree values at different occurrences from
being silently identified. -/
def Policy (N : Type*) : Type _ :=
  (path : List ℕ) → (mover : N) →
    (arity : ℕ) →
    (child : Fin (arity + 1) → StochasticGameTree N) →
      Fin (arity + 1)

/-- The head-selecting policy, useful when player choices are irrelevant. -/
def headPolicy : Policy N :=
  fun _path _mover arity _child =>
    ⟨0, Nat.zero_lt_succ arity⟩

/-- Embed an ordinary no-chance real-payoff `GameTree` into the stochastic
tree layer. -/
noncomputable def ofGameTree : GameTree N ℝ → StochasticGameTree N
  | tree =>
      GameTree.rec
        (motive_1 := fun _ => StochasticGameTree N)
        (motive_2 := fun _ => List (StochasticGameTree N))
        (fun payoff => StochasticGameTree.Leaf payoff)
        (fun mover _head _tail compiledHead compiledTail =>
          StochasticGameTree.Player mover compiledTail.length
            (childrenOfList compiledHead compiledTail))
        []
        (fun _head _tail compiledHead compiledTail =>
          compiledHead :: compiledTail)
        tree

/-- Fuel-bounded expected payoff under an occurrence-sensitive pure policy.

If fuel runs out, the default payoff is zero. At chance nodes this is the
finite expectation under the constructor's normalized `PMF`; callers choose
the horizon explicitly through `expectedPayoffAtFuel`. -/
noncomputable def expectedPayoffWithFuel (fuel : ℕ) (policy : Policy N)
    (path : List ℕ) (g : StochasticGameTree N) (i : N) : ℝ :=
  match fuel with
  | 0 => 0
  | n + 1 =>
      match g with
      | Leaf p => p i
      | Player mover arity child =>
          let choice := policy path mover arity child
          expectedPayoffWithFuel n policy
            (path ++ [choice.1]) (child choice) i
      | Chance arity child law =>
          ∑ choice : Fin (arity + 1),
            (law choice).toReal *
              expectedPayoffWithFuel n policy
                (path ++ [choice.1]) (child choice) i

/-- Expected payoff from the root at an explicit finite horizon.

The horizon remains explicit because a branching function is an opaque Lean
function: the inductive value alone does not expose a computable maximum depth
without an additional certificate. No claim is made that an arbitrary fuel
value reaches every leaf. -/
noncomputable def expectedPayoffAtFuel (fuel : ℕ) (policy : Policy N)
    (g : StochasticGameTree N) (i : N) : ℝ :=
  expectedPayoffWithFuel fuel policy [] g i

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

theorem fairCoin_expected_player0 :
    expectedPayoffAtFuel 2 (headPolicy : Policy (Fin 2))
      fairCoinGame 0 = 1 / 2 := by
  simp only [expectedPayoffAtFuel, expectedPayoffWithFuel, fairCoinGame,
    fairCoinLaw_apply, Nat.reduceAdd]
  rw [Fin.sum_univ_two]
  simp

end StochasticGameTree
