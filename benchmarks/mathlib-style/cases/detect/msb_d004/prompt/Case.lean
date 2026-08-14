import Mathlib.Algebra.GroupWithZero.Range

/-!
# Pilot case module
-/

namespace MathlibStylePilot.MsbD004

variable {R Γ₀ : Type*} [MonoidWithZero R] [CommGroupWithZero Γ₀]

def classBasedApply {F : Type*} [FunLike F R Γ₀] [MonoidWithZeroHomClass F R Γ₀]
    (f : F) (r : R) : Γ₀ :=
  f r

end MathlibStylePilot.MsbD004
