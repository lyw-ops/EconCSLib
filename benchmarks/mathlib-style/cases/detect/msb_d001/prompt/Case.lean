import Mathlib

/-!
# Pilot case module
-/

namespace MathlibStylePilot.MsbD001

theorem duplicateEvidence (p : Prop) (hp : p) : p ∧ p := by
  constructor

  · exact hp
  · exact hp

end MathlibStylePilot.MsbD001
