import Mathlib.Data.List.Basic

/-!
# EvE Mathlib-style repair smoke seed

This public synthetic file contains one deliberately targeted style issue.
-/

namespace EconCSLibEvESmoke

universe u

/-- Apply an endofunction twice. -/
def applyTwice {α : Type u} (f : α → α) (x : α) : α :=
  f $ f x

end EconCSLibEvESmoke
