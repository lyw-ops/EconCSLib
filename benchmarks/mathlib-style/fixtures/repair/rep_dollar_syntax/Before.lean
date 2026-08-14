import Mathlib.Data.List.Basic

/-!
# Repair application-syntax case (before)

This synthetic file contains the targeted pre-repair expression.
-/

namespace MathlibStyleDistillation.Repair.Before

universe u

/-- Apply an endofunction twice. -/
def applyTwice {α : Type u} (f : α → α) (x : α) : α :=
  f $ f x

end MathlibStyleDistillation.Repair.Before
