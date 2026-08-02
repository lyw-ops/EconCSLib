/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled

/-!
# Payoff-free lawful subgames

Occurrence-sensitive continuations, lawful subgame roots, selected subgame
systems, and complete subgame systems for `ControlledObservedGame`. Root
presentation remains an external choice, distinct from structural lawfulness.
Bijective player relabeling preserves and reflects root lawfulness and
transports both selected and complete systems without changing histories.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N M : Type*} {G : ControlledObservedGame N}

/-! ## Payoff-free lawful subgames -/

/-- `current` is an occurrence-sensitive continuation of `root`. -/
def IsContinuationOf
    (G : ControlledObservedGame N)
    (root current : G.base.History) : Prop :=
  Arena.Reachable G.base.unfold.toArena root current

/-- Every complete history is its own continuation. -/
theorem IsContinuationOf.refl
    (G : ControlledObservedGame N)
    (root : G.base.History) :
    G.IsContinuationOf root root :=
  by
    change Arena.Reachable G.base.unfold.toArena root root
    exact @Arena.Reachable.refl G.base.unfold.toArena root

/-- Information-set conditions making one complete history a lawful standard
subgame root. The definition is entirely payoff-free. -/
structure IsLawfulSubgameRoot
    (G : ControlledObservedGame N)
    (root : G.base.History) : Prop where
  /-- A proper player-controlled root has singleton decision information. -/
  root_information_singleton :
    root ≠ Arena.HistoryFrom.nil G.base.toArena G.base.init →
      ∀ (i : N) (hmover : G.base.mover root.1 = some i)
      (other : G.base.History)
      (hother : G.base.mover other.1 = some i),
      G.infoAt root i hmover =
          G.infoAt other i hother →
        other = root
  /-- Every information set encountered after entry stays wholly inside the
  continuation. -/
  information_closed :
    ∀ current, G.IsContinuationOf root current →
      ∀ (i : N) (hmover : G.base.mover current.1 = some i)
        (other : G.base.History)
        (hother : G.base.mover other.1 = some i),
        G.infoAt current i hmover =
            G.infoAt other i hother →
          G.IsContinuationOf root other

/-- Bijective player relabeling preserves and reflects structural subgame
lawfulness.

The proof transports mover witnesses through the player equivalence. Arena
histories and continuation reachability are unchanged, while the dependent
information-state equalities are converted using the equivalence inverse and
proof irrelevance. -/
theorem isLawfulSubgameRoot_relabelPlayers_iff
    (G : ControlledObservedGame N)
    (e : M ≃ N) (root : G.base.History) :
    (G.relabelPlayers e).IsLawfulSubgameRoot root ↔
      G.IsLawfulSubgameRoot root := by
  constructor
  · intro h
    constructor
    · intro hproper i hmover other hother hinfo
      have hmover' :
          (G.relabelPlayers e).base.mover root.1 =
            some (e.symm i) := by
        simp [hmover]
      have hother' :
          (G.relabelPlayers e).base.mover other.1 =
            some (e.symm i) := by
        simp [hother]
      apply h.root_information_singleton hproper
        (e.symm i) hmover' other hother'
      change
        G.infoAt root (e (e.symm i)) _ =
          G.infoAt other (e (e.symm i)) _
      convert hinfo using 1
      · exact congrArg G.InfoState (e.apply_symm_apply i)
      · congr
        · exact e.apply_symm_apply i
        · apply proof_irrel_heq
      · congr
        · exact e.apply_symm_apply i
        · apply proof_irrel_heq
    · intro current hcurrent i hmover other hother hinfo
      have hmover' :
          (G.relabelPlayers e).base.mover current.1 =
            some (e.symm i) := by
        simp [hmover]
      have hother' :
          (G.relabelPlayers e).base.mover other.1 =
            some (e.symm i) := by
        simp [hother]
      apply h.information_closed current hcurrent
        (e.symm i) hmover' other hother'
      change
        G.infoAt current (e (e.symm i)) _ =
          G.infoAt other (e (e.symm i)) _
      convert hinfo using 1
      · exact congrArg G.InfoState (e.apply_symm_apply i)
      · congr
        · exact e.apply_symm_apply i
        · apply proof_irrel_heq
      · congr
        · exact e.apply_symm_apply i
        · apply proof_irrel_heq
  · intro h
    constructor
    · intro hproper i hmover other hother hinfo
      have hmover' : G.base.mover root.1 = some (e i) := by
        have mapped := congrArg (Option.map e) hmover
        simpa using mapped
      have hother' : G.base.mover other.1 = some (e i) := by
        have mapped := congrArg (Option.map e) hother
        simpa using mapped
      apply h.root_information_singleton hproper
        (e i) hmover' other hother'
      simpa using hinfo
    · intro current hcurrent i hmover other hother hinfo
      have hmover' : G.base.mover current.1 = some (e i) := by
        have mapped := congrArg (Option.map e) hmover
        simpa using mapped
      have hother' : G.base.mover other.1 = some (e i) := by
        have mapped := congrArg (Option.map e) hother
        simpa using mapped
      apply h.information_closed current hcurrent
        (e i) hmover' other hother'
      simpa using hinfo

/-- An explicit selection of payoff-free lawful subgame roots. -/
