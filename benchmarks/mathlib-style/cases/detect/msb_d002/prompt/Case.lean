import Mathlib.RingTheory.Valuation.RankOne

/-!
# Pilot case module
-/

namespace MathlibStylePilot.MsbD002

open scoped NNReal

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

class RankLEOne (v : Valuation R Γ₀) where
  hom' : MonoidWithZeroHom.ValueGroup₀ v →*₀ ℝ≥0
  strictMono' : StrictMono hom'

end MathlibStylePilot.MsbD002
