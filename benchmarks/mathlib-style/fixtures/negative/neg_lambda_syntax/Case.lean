import Mathlib.Data.List.Basic

/-!
# Negative anonymous-function syntax case

This synthetic file intentionally contains one style violation.
-/

namespace MathlibStyleDistillation.Negative

/-- Double every natural number in a list. -/
def doubleEntries (xs : List ℕ) : List ℕ :=
  xs.map (λ n => n + n)

end MathlibStyleDistillation.Negative
