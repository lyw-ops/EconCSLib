import Mathlib

/-!
# Pilot case module
-/

namespace MathlibStylePilot.MsbP005

theorem witnessA {α : Type*} (x : α) : ∃ y, y = x := by
  apply Exists.intro x
  rfl

theorem witnessB {α : Type*} (x : α) : ∃ y, y = x := by
  refine ⟨x, rfl⟩

end MathlibStylePilot.MsbP005
