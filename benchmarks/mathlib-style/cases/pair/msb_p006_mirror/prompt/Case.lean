import Mathlib.Algebra.Order.GroupWithZero.WithZero

/-!
# Pilot case module
-/

namespace MathlibStylePilot.MsbP006

variable {α : Type*} [LinearOrderedCommGroupWithZero α]

def localWithZeroUnitsA : WithZero αˣ ≃o α where
  __ := WithZero.withZeroUnitsEquiv
  map_rel_iff' := WithZero.withZeroUnitsEquiv_strictMono.le_iff_le

abbrev localWithZeroUnitsB : WithZero αˣ ≃o α :=
  OrderIso.withZeroUnits

end MathlibStylePilot.MsbP006
