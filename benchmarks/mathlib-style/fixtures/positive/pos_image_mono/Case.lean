import Mathlib.Data.Set.Lattice

/-!
# Positive image-monotonicity case

This synthetic smoke case reuses the existing set-image API.
-/

namespace MathlibStyleDistillation.Positive

universe u v

variable {α : Type u} {β : Type v} {f : α → β} {s t : Set α}

/-- Images preserve set inclusion. -/
theorem image_mono_of_subset (hst : s ⊆ t) : f '' s ⊆ f '' t :=
  Set.image_mono hst

end MathlibStyleDistillation.Positive
