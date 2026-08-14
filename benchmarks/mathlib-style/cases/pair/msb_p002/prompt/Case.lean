import Mathlib.Data.List.Basic

/-!
# Pilot case module
-/

namespace MathlibStylePilot.MsbP002

def applyTwiceA {α : Type*} (f : α → α) (x : α) : α :=
  f $ f x

def applyTwiceB {α : Type*} (f : α → α) (x : α) : α :=
  f <| f x

end MathlibStylePilot.MsbP002
