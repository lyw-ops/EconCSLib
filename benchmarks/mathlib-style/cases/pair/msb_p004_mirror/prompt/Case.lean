import Mathlib.Data.Int.Cast.Lemmas

/-!
# Pilot case module
-/

namespace MathlibStylePilot.MsbP004

theorem castSelfA (n : ℕ) : (n : ℤ) = n := by
  change Int.ofNat n = Int.ofNat n
  rfl

theorem castSelfB (n : ℕ) : (n : ℤ) = n := by
  rfl

end MathlibStylePilot.MsbP004
