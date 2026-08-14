import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Pilot case module
-/

namespace Valuation.IsRankOneDiscrete

open MonoidWithZeroHom Set Subgroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable {A : Type*} [Ring A] (v : Valuation A Γ) [IsRankOneDiscrete v]

lemma pilot_generator'_zpowers_eq_top : (zpowers (generator' v)) = ⊤ := by
  rw [← (Subgroup.map_injective (valueGroup v).subtype_injective).eq_iff,
    MonoidHom.map_zpowers, subtype_apply, ← MonoidHom.range_eq_map,
    Subgroup.subtype_range]
  apply generator_zpowers_eq_valueGroup

end Valuation.IsRankOneDiscrete
