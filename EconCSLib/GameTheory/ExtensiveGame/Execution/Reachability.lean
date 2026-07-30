/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic

/-!
# EconCSLib.GameTheory.ExtensiveGame.Execution.Reachability

Reachability for the Arena extensive-game model.

This module contains the representation-neutral path relation and the
initial-state specialization used by execution infrastructure. Historical
subgame and re-rooting constructions import this module, but canonical
execution modules need not import those historical APIs.

## Main definitions

* `Arena.Reachable` — finite transition reachability between Arena states.
* `ExtensiveGame.IsReachable` — reachability from an extensive game's initial
  state.
-/

namespace Arena

/-- A state `t` is reachable from `s` if there is a path of transitions from
`s` to `t`. -/
inductive Reachable (A : Arena) : A.State → A.State → Prop where
  | refl (s : A.State) : Reachable A s s
  | step {s t : A.State} (a : A.Action s)
      (h : Reachable A (A.next s a) t) :
      Reachable A s t

/-- Reachable is transitive. -/
theorem Reachable.trans {A : Arena} {s t u : A.State}
    (h1 : A.Reachable s t) (h2 : A.Reachable t u) :
    A.Reachable s u := by
  induction h1 with
  | refl => exact h2
  | step a _ ih => exact Reachable.step a (ih h2)

/-- One step extends reachability. -/
theorem Reachable.tail {A : Arena} {s t : A.State}
    (h : A.Reachable s t) (a : A.Action t) :
    A.Reachable s (A.next t a) :=
  h.trans (Reachable.step a (Reachable.refl _))

end Arena

namespace ExtensiveGame

variable {N : Type*} {U : Type*}

/-- A state is reachable in the game if it is reachable from `init`. -/
def IsReachable (G : ExtensiveGame N U) (s : G.State) : Prop :=
  Arena.Reachable G.toArena G.init s

/-- The initial state is always reachable. -/
theorem isReachable_init (G : ExtensiveGame N U) : G.IsReachable G.init :=
  Arena.Reachable.refl _

/-- If `s` is reachable and we take action `a`, then `next s a` is reachable. -/
theorem IsReachable.next {G : ExtensiveGame N U} {s : G.State}
    (h : G.IsReachable s) (a : G.Action s) :
    G.IsReachable (G.next s a) :=
  h.tail a

end ExtensiveGame
