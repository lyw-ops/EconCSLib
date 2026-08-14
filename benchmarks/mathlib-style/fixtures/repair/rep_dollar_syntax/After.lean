import Mathlib.Data.List.Basic

/-!
# Repair application-syntax case (after)

This synthetic file contains the preferred repaired expression.
-/

namespace MathlibStyleDistillation.Repair.After

universe u

/-- Apply an endofunction twice. -/
def applyTwice {α : Type u} (f : α → α) (x : α) : α :=
  f <| f x

end MathlibStyleDistillation.Repair.After
