/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.CertifiedPathApproximation
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Effective discounted path utilities

This module gives a measure-free algorithm for discounted utilities of
coherent effective path laws.  A utility supplies an executable rational
reward at every absolute time and state or action-recording event, a
nonnegative rational discount `γ < 1`, and a uniform nonnegative rational
reward bound `B`.

At horizon `H`, the algorithm evaluates exactly the first `H` rewards at
offsets `0, ..., H - 1` from the supplied absolute `start`.  Its declared
geometric tail radius is

`B * γ ^ H / (1 - γ)`.

The resulting state and event objects are ordinary
`PrefixApproximationScheme`s, so the exact centers, rational intervals, and
budgeted or least-horizon searches from `CertifiedPathApproximation` apply
directly.  The radius is proved to vanish for every `γ < 1` and therefore
supplies a finite acceptable horizon for every positive rational tolerance.

The stored per-period bound explains the geometric schedule but this pure
layer deliberately does not assert that a particular infinite-path integral
lies in one of its intervals.  Such a conclusion requires a separate
semantic certificate identifying the infinite discounted series and proving
the finite-prefix error estimate.

For a supplied horizon law, evaluating one center is linear in both `H` and
the law's weighted occurrence list.  Producing that law can still grow
exponentially with horizon and branching degree.  Radius search itself uses
only exact rational arithmetic and performs at most the supplied number of
comparisons.

## Main definitions and results

* `DiscountedPathUtility.geometricTailRadius` and its vanishing proof;
* `StateDiscountedPathUtility` and `EventDiscountedPathUtility`;
* exact finite discounted observables and centers at offsets `0, ..., H - 1`;
* direct conversion to the A15 prefix-approximation schemes;
* state-to-event projection and policy-execution correctness.
-/

namespace KernelArena

universe uS uA

namespace DiscountedPathUtility

/-- Executable geometric tail schedule `B * γ^H / (1 - γ)`.  Its convergence
meaning is established below from `γ < 1`; target-error meaning still needs a
separate semantic discounted-series certificate. -/
def geometricTailRadius (discount bound : ℚ≥0) : ApproximationRadius :=
  fun horizon => bound * discount ^ horizon / (1 - discount)

@[simp]
theorem geometricTailRadius_apply (discount bound : ℚ≥0) (horizon : ℕ) :
    geometricTailRadius discount bound horizon =
      bound * discount ^ horizon / (1 - discount) :=
  rfl

/-- The denominator of the geometric tail is positive at every admitted
discount. -/
theorem one_sub_discount_pos {discount : ℚ≥0}
    (hdiscount : discount < 1) : 0 < 1 - discount := by
  change (0 : ℚ) < ((1 - discount : ℚ≥0) : ℚ)
  rw [NNRat.coe_sub (le_of_lt hdiscount)]
  exact sub_pos.mpr (show (discount : ℚ) < 1 from hdiscount)

/-- The geometric tail schedule vanishes at every rational discount below
one.  The proof is Archimedean and supplies no oracle for an external target
expectation. -/
theorem geometricTailRadius_vanishes
    {discount bound : ℚ≥0} (hdiscount : discount < 1) :
    (geometricTailRadius discount bound).Vanishes := by
  intro tolerance htolerance
  by_cases hbound : bound = 0
  · refine ⟨0, ?_⟩
    intro horizon _
    simp [geometricTailRadius, hbound]
  · have hboundPos : 0 < bound := pos_iff_ne_zero.mpr hbound
    have hdenominator : 0 < 1 - discount :=
      one_sub_discount_pos hdiscount
    let threshold : ℚ≥0 := tolerance * (1 - discount) / bound
    have hthreshold : 0 < threshold := by
      dsimp only [threshold]
      exact div_pos (mul_pos htolerance hdenominator) hboundPos
    obtain ⟨cutoff, hcutoff⟩ :=
      exists_pow_lt₀ hdiscount (Units.mk0 threshold hthreshold.ne')
    refine ⟨cutoff, ?_⟩
    intro horizon hcutoffHorizon
    have hpower : discount ^ horizon ≤ discount ^ cutoff :=
      pow_le_pow_of_le_one (show 0 ≤ discount from bot_le)
        (le_of_lt hdiscount) hcutoffHorizon
    apply LT.lt.le
    apply (div_lt_iff₀ hdenominator).2
    calc
      bound * discount ^ horizon ≤ bound * discount ^ cutoff :=
        mul_le_mul_of_nonneg_left hpower (show 0 ≤ bound from bot_le)
      _ < bound * threshold :=
        mul_lt_mul_of_pos_left hcutoff hboundPos
      _ = tolerance * (1 - discount) := by
        dsimp only [threshold]
        exact mul_div_cancel₀ (tolerance * (1 - discount)) hbound

/-- An explicit finite coordinate for offset `0 ≤ offset < horizon`, measured
from the absolute start. -/
def coordinate (start horizon : ℕ) (offset : Fin horizon) :
    Fin (start + horizon + 1) :=
  ⟨start + offset, by omega⟩

@[simp]
theorem coordinate_val (start horizon : ℕ) (offset : Fin horizon) :
    (coordinate start horizon offset).val = start + offset.val :=
  rfl

end DiscountedPathUtility

/-- Executable discounted state reward with a uniform per-period bound. -/
structure StateDiscountedPathUtility (A : KernelArena) where
  /-- Rational reward at an absolute time and state. -/
  reward : ℕ → A.State → ℚ
  /-- Nonnegative rational discount. -/
  discount : ℚ≥0
  /-- Strict discount needed for a finite geometric tail. -/
  discount_lt_one : discount < 1
  /-- Uniform nonnegative rational absolute reward bound. -/
  bound : ℚ≥0
  /-- Every executable one-period reward obeys the supplied bound. -/
  reward_abs_le : ∀ time state, |reward time state| ≤ (bound : ℚ)

end KernelArena
