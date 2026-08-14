import Mathlib

/-!
# Pilot case module
-/

namespace MathlibStylePilot.MsbL002

private def implementationHelper (n : ℕ) : ℕ := n + 1

def publicValue : ℕ := implementationHelper 0

end MathlibStylePilot.MsbL002
