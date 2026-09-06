/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Executable rational enclosures

This module provides the arithmetic foundation for effective probability
interfaces.  A `RatEnclosure` is a closed interval with rational endpoints,
and a `RatOracle` returns such an interval at every positive rational
tolerance.  The oracle contract bounds the interval width by the requested
tolerance; a separate semantic layer can state which real quantity lies in
all returned intervals.

All definitions here are executable and use exact rational arithmetic.
There is deliberately no dependency on measures, kernels, integration, or
real-valued semantics.

The oracle operations split an addition or subtraction tolerance equally
between their two inputs.  Scaling a nonzero oracle queries its input at
`tolerance / |factor|`; scaling by zero returns the exact zero oracle.
-/

namespace EffectiveProbability

/-- A nonempty closed interval with rational endpoints. -/
structure RatEnclosure where
  /-- Lower endpoint. -/
  lower : ℚ
  /-- Upper endpoint. -/
  upper : ℚ
  /-- The endpoint order certifying that the interval is nonempty. -/
  lower_le_upper : lower ≤ upper

namespace RatEnclosure

/-- Exact rational width of an enclosure. -/
def width (interval : RatEnclosure) : ℚ :=
  interval.upper - interval.lower

/-- A rational value belongs to an enclosure exactly when it lies between
the two endpoints. -/
def Contains (interval : RatEnclosure) (value : ℚ) : Prop :=
  interval.lower ≤ value ∧ value ≤ interval.upper

/-- The singleton enclosure containing an exact rational value. -/
def exact (value : ℚ) : RatEnclosure :=
  ⟨value, value, le_rfl⟩

/-- Pointwise negation of a rational enclosure. -/
def neg (interval : RatEnclosure) : RatEnclosure :=
  ⟨-interval.upper, -interval.lower, neg_le_neg interval.lower_le_upper⟩

/-- Minkowski sum of two rational enclosures. -/
def add (left right : RatEnclosure) : RatEnclosure :=
  ⟨left.lower + right.lower, left.upper + right.upper,
    add_le_add left.lower_le_upper right.lower_le_upper⟩

/-- Minkowski difference of two rational enclosures. -/
def sub (left right : RatEnclosure) : RatEnclosure :=
  left.add right.neg

/-- Scale an enclosure, reversing its endpoints when the factor is negative. -/
def scale (factor : ℚ) (interval : RatEnclosure) : RatEnclosure :=
  if hfactor : 0 ≤ factor then
    ⟨factor * interval.lower, factor * interval.upper,
      mul_le_mul_of_nonneg_left interval.lower_le_upper hfactor⟩
  else
    ⟨factor * interval.upper, factor * interval.lower,
      mul_le_mul_of_nonpos_left interval.lower_le_upper
        (le_of_lt (lt_of_not_ge hfactor))⟩

@[simp]
theorem exact_lower (value : ℚ) : (exact value).lower = value := rfl

@[simp]
theorem exact_upper (value : ℚ) : (exact value).upper = value := rfl

@[simp]
theorem neg_lower (interval : RatEnclosure) :
    interval.neg.lower = -interval.upper := rfl

@[simp]
theorem neg_upper (interval : RatEnclosure) :
    interval.neg.upper = -interval.lower := rfl

@[simp]
theorem add_lower (left right : RatEnclosure) :
    (left.add right).lower = left.lower + right.lower := rfl

@[simp]
theorem add_upper (left right : RatEnclosure) :
    (left.add right).upper = left.upper + right.upper := rfl

@[simp]
theorem sub_lower (left right : RatEnclosure) :
    (left.sub right).lower = left.lower - right.upper := by
  simp [sub, sub_eq_add_neg]

@[simp]
theorem sub_upper (left right : RatEnclosure) :
    (left.sub right).upper = left.upper - right.lower := by
  simp [sub, sub_eq_add_neg]

@[simp]
theorem scale_lower_of_nonneg (interval : RatEnclosure) {factor : ℚ}
    (hfactor : 0 ≤ factor) :
    (interval.scale factor).lower = factor * interval.lower := by
  simp [scale, hfactor]

@[simp]
theorem scale_upper_of_nonneg (interval : RatEnclosure) {factor : ℚ}
    (hfactor : 0 ≤ factor) :
    (interval.scale factor).upper = factor * interval.upper := by
  simp [scale, hfactor]

@[simp]
theorem scale_lower_of_neg (interval : RatEnclosure) {factor : ℚ}
    (hfactor : factor < 0) :
    (interval.scale factor).lower = factor * interval.upper := by
  simp [scale, not_le.mpr hfactor]

@[simp]
theorem scale_upper_of_neg (interval : RatEnclosure) {factor : ℚ}
    (hfactor : factor < 0) :
    (interval.scale factor).upper = factor * interval.lower := by
  simp [scale, not_le.mpr hfactor]

/-- Every certified enclosure has nonnegative width. -/
theorem width_nonneg (interval : RatEnclosure) : 0 ≤ interval.width := by
  exact sub_nonneg.mpr interval.lower_le_upper

@[simp]
theorem width_exact (value : ℚ) : (exact value).width = 0 := by
  simp [width]

@[simp]
theorem width_neg (interval : RatEnclosure) :
    interval.neg.width = interval.width := by
  simp [width, neg, sub_eq_add_neg]
  ring

@[simp]
theorem width_add (left right : RatEnclosure) :
    (left.add right).width = left.width + right.width := by
  simp [width, add]
  ring

@[simp]
theorem width_sub (left right : RatEnclosure) :
    (left.sub right).width = left.width + right.width := by
  simp [sub]

@[simp]
theorem width_scale (factor : ℚ) (interval : RatEnclosure) :
    (interval.scale factor).width = |factor| * interval.width := by
  by_cases hfactor : 0 ≤ factor
  · simp [scale, width, hfactor, abs_of_nonneg hfactor]
    ring
  · have hnegative : factor < 0 := lt_of_not_ge hfactor
    simp [scale, width, hfactor, abs_of_neg hnegative]
    ring

@[simp]
theorem contains_exact (value : ℚ) : (exact value).Contains value := by
  simp [Contains]

/-- Negation preserves interval membership. -/
theorem Contains.neg {interval : RatEnclosure} {value : ℚ}
    (hvalue : interval.Contains value) :
    interval.neg.Contains (-value) := by
  rcases hvalue with ⟨hlower, hupper⟩
  exact ⟨neg_le_neg hupper, neg_le_neg hlower⟩

/-- Addition preserves interval membership. -/
theorem Contains.add {left right : RatEnclosure} {x y : ℚ}
    (hx : left.Contains x) (hy : right.Contains y) :
    (left.add right).Contains (x + y) := by
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

/-- Subtraction preserves interval membership. -/
theorem Contains.sub {left right : RatEnclosure} {x y : ℚ}
    (hx : left.Contains x) (hy : right.Contains y) :
    (left.sub right).Contains (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

/-- Rational scaling preserves interval membership. -/
theorem Contains.scale {interval : RatEnclosure} {value factor : ℚ}
    (hvalue : interval.Contains value) :
    (interval.scale factor).Contains (factor * value) := by
  by_cases hfactor : 0 ≤ factor
  · simpa [Contains, scale, hfactor] using
      (show factor * interval.lower ≤ factor * value ∧
          factor * value ≤ factor * interval.upper from
        ⟨mul_le_mul_of_nonneg_left hvalue.1 hfactor,
          mul_le_mul_of_nonneg_left hvalue.2 hfactor⟩)
  · have hnegative : factor < 0 := lt_of_not_ge hfactor
    have hnonpos : factor ≤ 0 := hnegative.le
    change (interval.scale factor).lower ≤ factor * value ∧
      factor * value ≤ (interval.scale factor).upper
    rw [scale_lower_of_neg interval hnegative,
      scale_upper_of_neg interval hnegative]
    exact ⟨mul_le_mul_of_nonpos_left hvalue.2 hnonpos,
      mul_le_mul_of_nonpos_left hvalue.1 hnonpos⟩

end RatEnclosure

end EffectiveProbability
