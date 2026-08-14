import Mathlib

/-!
# Pilot case module
-/

namespace MathlibStylePilot.MsbD003

theorem transport {α : Sort*} {a b c : α} (hab : a = b) (hbc : b = c) : a = c := by
  erw [hab]
  exact hbc

end MathlibStylePilot.MsbD003
