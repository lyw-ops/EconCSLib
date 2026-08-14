import Mathlib.Data.List.Basic

/-!
# Pilot case module
-/

namespace MathlibStylePilot.MsbP001

def mapSuccA (xs : List ℕ) : List ℕ :=
  xs.map (fun x ↦ x + 1)

def mapSuccB (xs : List ℕ) : List ℕ :=
  xs.map (fun n ↦ n + 1)

end MathlibStylePilot.MsbP001
